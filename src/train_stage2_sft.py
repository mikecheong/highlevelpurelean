"""
Stage 2: Sketchpad Supervised Fine-Tuning (SFT) on 2,050 Lean-verified
`<sketchpad>...</sketchpad>` + pure Lean 4 proof examples.
Starts from `checkpoints/stage1_pure_lean_merged`, masks prompt tokens (`-100`)
so gradients focus purely on `<sketchpad>` reasoning and formal Lean 4 proofs,
uses length-bucketed batching + token-chunked cross-entropy on Apple MPS, and
merges the resulting LoRA adapter into `checkpoints/stage2_sketchpad_sft_merged`.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from typing import Dict, List, Tuple

import torch

from src.mps_lora_utils import (
    attach_lora,
    clear_mps_cache,
    compute_chunked_lm_loss,
    get_device,
    load_causal_lm,
    load_tokenizer,
    merge_and_save_checkpoint,
    render_chat_ids,
)


def tokenize_sft_dataset(
    jsonl_path: str,
    tokenizer,
    max_seq_len: int = 640,
) -> List[Tuple[List[int], List[int]]]:
    """
    Returns list of `(input_ids, labels)` where prompt tokens are masked as `-100`.
    """
    dataset: List[Tuple[List[int], List[int]]] = []
    with open(jsonl_path, "r", encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            row = json.loads(line)
            msgs = row["messages"]
            prompt_ids = render_chat_ids(tokenizer, msgs[:2], add_generation_prompt=True)
            full_ids = render_chat_ids(tokenizer, msgs, add_generation_prompt=False)
            if len(full_ids) > max_seq_len:
                full_ids = full_ids[:max_seq_len]
            if len(prompt_ids) >= len(full_ids):
                continue
            labels = [-100] * len(prompt_ids) + full_ids[len(prompt_ids) :]
            dataset.append((full_ids, labels))
    return dataset


def collate_pad(
    batch: List[Tuple[List[int], List[int]]],
    pad_id: int,
    device: str,
) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    max_len = max(len(x[0]) for x in batch)
    bsz = len(batch)
    input_ids = torch.full((bsz, max_len), pad_id, dtype=torch.long, device=device)
    attn_mask = torch.zeros((bsz, max_len), dtype=torch.long, device=device)
    labels = torch.full((bsz, max_len), -100, dtype=torch.long, device=device)
    for i, (ids, lbs) in enumerate(batch):
        n = len(ids)
        input_ids[i, :n] = torch.tensor(ids, dtype=torch.long, device=device)
        attn_mask[i, :n] = 1
        labels[i, :n] = torch.tensor(lbs, dtype=torch.long, device=device)
    return input_ids, attn_mask, labels


@torch.no_grad()
def evaluate_sft(
    model,
    val_data: List[Tuple[List[int], List[int]]],
    pad_id: int,
    device: str,
    batch_size: int = 4,
) -> Dict[str, float]:
    model.eval()
    total_nll = 0.0
    total_toks = 0
    for i in range(0, len(val_data), batch_size):
        batch = val_data[i : i + batch_size]
        inp, attn, lbs = collate_pad(batch, pad_id, device)
        loss, n_tok = compute_chunked_lm_loss(model, inp, attn, lbs, token_chunk_size=128)
        total_nll += float(loss.item()) * n_tok
        total_toks += n_tok
    mean_loss = total_nll / max(1, total_toks)
    ppl = math.exp(min(20.0, mean_loss))
    model.train()
    return {"val_loss": round(mean_loss, 4), "val_ppl": round(ppl, 4), "val_tokens": total_toks}


def make_length_bucketed_batches(
    data: List[Tuple[List[int], List[int]]],
    batch_size: int,
    seed: int,
    pool_multiplier: int = 16,
) -> List[List[Tuple[List[int], List[int]]]]:
    """
    Shuffle inside length Mega-pools to minimize padding waste while preserving stochasticity.
    """
    rng = random.Random(seed)
    items = list(data)
    rng.shuffle(items)
    pool_size = batch_size * pool_multiplier
    batches: List[List[Tuple[List[int], List[int]]]] = []
    for i in range(0, len(items), pool_size):
        pool = items[i : i + pool_size]
        pool.sort(key=lambda x: len(x[0]))
        for j in range(0, len(pool), batch_size):
            batches.append(pool[j : j + batch_size])
    rng.shuffle(batches)
    return batches


def train_stage2_sft(
    stage1_model_dir: str = "checkpoints/stage1_pure_lean_merged",
    train_jsonl: str = "data/stage2_sketchpad_sft.jsonl",
    val_jsonl: str = "data/stage2_sketchpad_sft_val.jsonl",
    merged_out_dir: str = "checkpoints/stage2_sketchpad_sft_merged",
    adapter_out_dir: str = "checkpoints/stage2_sketchpad_sft_lora",
    metrics_path: str = "logs/stage2_sft_metrics.json",
    max_seq_len: int = 1472,
    epochs: int = 1,
    micro_batch_size: int = 1,
    grad_accum_steps: int = 8,
    lr: float = 1.8e-4,
    lora_r: int = 24,
    lora_alpha: int = 48,
    seed: int = 108,
) -> Dict:
    t0 = time.time()
    torch.manual_seed(seed)
    random.seed(seed)
    device = get_device()
    print(f"[Stage 2 SFT] Loading Stage 1 model from {stage1_model_dir} on {device} ...", flush=True)

    tokenizer = load_tokenizer(stage1_model_dir)
    train_data = tokenize_sft_dataset(train_jsonl, tokenizer, max_seq_len=max_seq_len)
    val_data = tokenize_sft_dataset(val_jsonl, tokenizer, max_seq_len=max_seq_len)
    val_data.sort(key=lambda x: len(x[0]))
    print(
        f"[Stage 2 SFT] Tokenized {len(train_data)} train and {len(val_data)} val sketchpad examples.",
        flush=True,
    )

    base = load_causal_lm(stage1_model_dir, device=device, dtype=torch.bfloat16, gradient_checkpointing=False)
    model = attach_lora(base, r=lora_r, lora_alpha=lora_alpha, lora_dropout=0.05, device=device)

    pad_id = tokenizer.pad_token_id
    init_eval = evaluate_sft(model, val_data, pad_id=pad_id, device=device, batch_size=micro_batch_size)
    print(f"[Stage 2 SFT] Initial Val: {init_eval}", flush=True)

    trainable_params = [p for p in model.parameters() if p.requires_grad]
    optimizer = torch.optim.AdamW(trainable_params, lr=lr, weight_decay=0.01)

    batches_per_epoch = math.ceil(len(train_data) / micro_batch_size)
    total_opt_steps = math.ceil((batches_per_epoch * epochs) / grad_accum_steps)
    warmup_steps = max(8, int(0.08 * total_opt_steps))

    def lr_lambda(step: int) -> float:
        if step < warmup_steps:
            return float(step + 1) / float(warmup_steps)
        prog = float(step - warmup_steps) / float(max(1, total_opt_steps - warmup_steps))
        return 0.1 + 0.9 * 0.5 * (1.0 + math.cos(math.pi * min(1.0, prog)))

    scheduler = torch.optim.lr_scheduler.LambdaLR(optimizer, lr_lambda)

    history: List[Dict] = [{"step": 0, **init_eval}]
    opt_step = 0
    accum_count = 0
    running_loss = 0.0
    running_batches = 0

    model.train()
    optimizer.zero_grad()

    for ep in range(epochs):
        ep_batches = make_length_bucketed_batches(
            train_data, batch_size=micro_batch_size, seed=seed + ep
        )
        for b_idx, batch in enumerate(ep_batches):
            inp, attn, lbs = collate_pad(batch, pad_id=pad_id, device=device)
            loss, _ = compute_chunked_lm_loss(model, inp, attn, lbs, token_chunk_size=128)
            (loss / float(grad_accum_steps)).backward()

            running_loss += float(loss.item())
            running_batches += 1
            accum_count += 1

            is_last = (b_idx + 1) == len(ep_batches)
            if accum_count >= grad_accum_steps or is_last:
                torch.nn.utils.clip_grad_norm_(trainable_params, max_norm=1.0)
                optimizer.step()
                scheduler.step()
                optimizer.zero_grad()
                opt_step += 1
                accum_count = 0
                if torch.backends.mps.is_available():
                    torch.mps.empty_cache()

                if opt_step % 20 == 0 or is_last:
                    if torch.backends.mps.is_available():
                        torch.mps.empty_cache()
                    avg_tr = running_loss / max(1, running_batches)
                    rec: Dict = {
                        "epoch": ep + 1,
                        "step": opt_step,
                        "total_steps": total_opt_steps,
                        "train_loss": round(avg_tr, 4),
                        "lr": round(scheduler.get_last_lr()[0], 7),
                        "elapsed_sec": round(time.time() - t0, 1),
                    }
                    if opt_step % 80 == 0 or is_last:
                        ev = evaluate_sft(model, val_data, pad_id=pad_id, device=device, batch_size=micro_batch_size)
                        rec.update(ev)
                    history.append(rec)
                    print(f"[Stage 2 SFT] {rec}", flush=True)
                    running_loss = 0.0
                    running_batches = 0

    final_eval = evaluate_sft(model, val_data, pad_id=pad_id, device=device, batch_size=micro_batch_size)
    print(f"[Stage 2 SFT] Final Val before merge: {final_eval}", flush=True)

    print(f"[Stage 2 SFT] Merging LoRA adapter into {merged_out_dir} ...", flush=True)
    merge_and_save_checkpoint(model, tokenizer, save_dir=merged_out_dir, adapter_dir=adapter_out_dir)

    os.makedirs(os.path.dirname(metrics_path), exist_ok=True)
    summary = {
        "stage": "stage2_sketchpad_sft",
        "source_model": stage1_model_dir,
        "merged_checkpoint": merged_out_dir,
        "adapter_checkpoint": adapter_out_dir,
        "train_examples": len(train_data),
        "val_examples": len(val_data),
        "epochs": epochs,
        "opt_steps": opt_step,
        "initial_val": init_eval,
        "final_val": final_eval,
        "elapsed_sec": round(time.time() - t0, 2),
        "history": history,
    }
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    print(f"[Stage 2 SFT] Completed in {summary['elapsed_sec']}s! Saved metrics to {metrics_path}", flush=True)
    clear_mps_cache()
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--epochs", type=int, default=1)
    parser.add_argument("--lr", type=float, default=1.8e-4)
    args = parser.parse_args()
    train_stage2_sft(epochs=args.epochs, lr=args.lr)
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(0)
