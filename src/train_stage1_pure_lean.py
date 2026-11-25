"""
Stage 1: Synthetic Pure Lean 4 Domain Training on Qwen/Qwen2.5-Coder-3B-Instruct.
Packs 1,620 Lean-4.36-verified pure Lean modules into 512-token sequences, trains
a rank-16 LoRA adapter across all attention & MLP projections on Apple MPS (bf16)
using memory-safe token-chunked cross-entropy, logs train/val loss & perplexity,
and merges the trained adapter into `checkpoints/stage1_pure_lean_merged`.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from typing import Dict, List

import torch

from src.mps_lora_utils import (
    DEFAULT_BASE_MODEL,
    attach_lora,
    clear_mps_cache,
    compute_chunked_lm_loss,
    get_device,
    load_causal_lm,
    load_tokenizer,
    merge_and_save_checkpoint,
)
from src.prompts import format_stage1_pure_lean_doc


def build_packed_blocks(
    corpus_path: str,
    tokenizer,
    seq_len: int = 512,
    seed: int = 42,
) -> List[List[int]]:
    rows: List[Dict] = []
    with open(corpus_path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                rows.append(json.loads(line))

    rng = random.Random(seed)
    rng.shuffle(rows)

    eos_id = tokenizer.eos_token_id
    stream: List[int] = []
    for r in rows:
        doc = format_stage1_pure_lean_doc(
            r["preamble"], r["theorem_header"], r["proof_body"], r["domain"]
        )
        ids = tokenizer.encode(doc, add_special_tokens=False)
        stream.extend(ids)
        stream.append(eos_id)

    blocks: List[List[int]] = []
    for i in range(0, len(stream) - seq_len, seq_len):
        blocks.append(stream[i : i + seq_len])
    return blocks


@torch.no_grad()
def evaluate_blocks(model, val_blocks: List[List[int]], device: str, batch_size: int = 2) -> Dict[str, float]:
    model.eval()
    total_loss_tok = 0.0
    total_toks = 0
    for i in range(0, len(val_blocks), batch_size):
        batch = val_blocks[i : i + batch_size]
        input_ids = torch.tensor(batch, dtype=torch.long, device=device)
        attn = torch.ones_like(input_ids)
        loss, n_tok = compute_chunked_lm_loss(model, input_ids, attn, input_ids, token_chunk_size=128)
        total_loss_tok += float(loss.item()) * n_tok
        total_toks += n_tok
    mean_loss = total_loss_tok / max(1, total_toks)
    ppl = math.exp(min(20.0, mean_loss))
    model.train()
    return {"val_loss": round(mean_loss, 4), "val_ppl": round(ppl, 4), "val_tokens": total_toks}


def train_stage1(
    base_model: str = DEFAULT_BASE_MODEL,
    corpus_path: str = "data/stage1_pure_lean.jsonl",
    merged_out_dir: str = "checkpoints/stage1_pure_lean_merged",
    adapter_out_dir: str = "checkpoints/stage1_pure_lean_lora",
    metrics_path: str = "logs/stage1_metrics.json",
    seq_len: int = 512,
    epochs: int = 1,
    micro_batch_size: int = 3,
    grad_accum_steps: int = 3,
    lr: float = 2.0e-4,
    lora_r: int = 16,
    lora_alpha: int = 32,
    seed: int = 42,
) -> Dict:
    t0 = time.time()
    torch.manual_seed(seed)
    random.seed(seed)
    device = get_device()
    print(f"[Stage 1] Using device={device}, base_model={base_model}", flush=True)

    tokenizer = load_tokenizer(base_model)
    blocks = build_packed_blocks(corpus_path, tokenizer, seq_len=seq_len, seed=seed)
    n_val = max(16, min(32, len(blocks) // 12))
    val_blocks = blocks[:n_val]
    train_blocks = blocks[n_val:]
    print(
        f"[Stage 1] Packed {len(blocks)} blocks of {seq_len} tokens "
        f"(train={len(train_blocks)}, val={len(val_blocks)})",
        flush=True,
    )

    base = load_causal_lm(base_model, device=device, dtype=torch.bfloat16, gradient_checkpointing=False)
    model = attach_lora(base, r=lora_r, lora_alpha=lora_alpha, lora_dropout=0.05, device=device)
    trainable = sum(p.numel() for p in model.parameters() if p.requires_grad)
    total_params = sum(p.numel() for p in model.parameters())
    print(
        f"[Stage 1] LoRA trainable params: {trainable:,} / {total_params:,} "
        f"({100.0 * trainable / total_params:.2f}%)",
        flush=True,
    )

    init_eval = evaluate_blocks(model, val_blocks, device=device, batch_size=micro_batch_size)
    print(f"[Stage 1] Initial Val: {init_eval}", flush=True)

    trainable_params = [p for p in model.parameters() if p.requires_grad]
    optimizer = torch.optim.AdamW(trainable_params, lr=lr, weight_decay=0.01)

    micro_steps_per_epoch = math.ceil(len(train_blocks) / micro_batch_size)
    total_opt_steps = math.ceil((micro_steps_per_epoch * epochs) / grad_accum_steps)
    warmup_steps = max(4, int(0.08 * total_opt_steps))

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
        ep_blocks = list(train_blocks)
        random.Random(seed + ep).shuffle(ep_blocks)

        for b_idx in range(0, len(ep_blocks), micro_batch_size):
            batch = ep_blocks[b_idx : b_idx + micro_batch_size]
            input_ids = torch.tensor(batch, dtype=torch.long, device=device)
            attn = torch.ones_like(input_ids)

            loss, _ = compute_chunked_lm_loss(
                model, input_ids, attn, input_ids, token_chunk_size=128
            )
            scaled_loss = loss / float(grad_accum_steps)
            scaled_loss.backward()

            running_loss += float(loss.item())
            running_batches += 1
            accum_count += 1

            is_last_in_ep = (b_idx + micro_batch_size) >= len(ep_blocks)
            if accum_count >= grad_accum_steps or is_last_in_ep:
                torch.nn.utils.clip_grad_norm_(trainable_params, max_norm=1.0)
                optimizer.step()
                scheduler.step()
                optimizer.zero_grad()
                opt_step += 1
                accum_count = 0

                if opt_step % 10 == 0 or is_last_in_ep:
                    avg_tr = running_loss / max(1, running_batches)
                    cur_lr = scheduler.get_last_lr()[0]
                    elapsed = time.time() - t0
                    rec: Dict = {
                        "epoch": ep + 1,
                        "step": opt_step,
                        "total_steps": total_opt_steps,
                        "train_loss": round(avg_tr, 4),
                        "lr": round(cur_lr, 7),
                        "elapsed_sec": round(elapsed, 1),
                    }
                    if opt_step % 35 == 0 or is_last_in_ep:
                        ev = evaluate_blocks(model, val_blocks, device=device, batch_size=micro_batch_size)
                        rec.update(ev)
                    history.append(rec)
                    print(f"[Stage 1] {rec}", flush=True)
                    running_loss = 0.0
                    running_batches = 0

    final_eval = evaluate_blocks(model, val_blocks, device=device, batch_size=micro_batch_size)
    print(f"[Stage 1] Final Val before merge: {final_eval}", flush=True)

    print(f"[Stage 1] Merging LoRA adapter into {merged_out_dir} ...", flush=True)
    merge_and_save_checkpoint(model, tokenizer, save_dir=merged_out_dir, adapter_dir=adapter_out_dir)

    os.makedirs(os.path.dirname(metrics_path), exist_ok=True)
    summary = {
        "stage": "stage1_pure_lean",
        "base_model": base_model,
        "merged_checkpoint": merged_out_dir,
        "adapter_checkpoint": adapter_out_dir,
        "seq_len": seq_len,
        "epochs": epochs,
        "train_blocks": len(train_blocks),
        "val_blocks": len(val_blocks),
        "opt_steps": opt_step,
        "initial_val": init_eval,
        "final_val": final_eval,
        "elapsed_sec": round(time.time() - t0, 2),
        "history": history,
    }
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)
    print(f"[Stage 1] Completed in {summary['elapsed_sec']}s! Saved metrics to {metrics_path}", flush=True)
    clear_mps_cache()
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--epochs", type=int, default=1)
    parser.add_argument("--seq-len", type=int, default=512)
    parser.add_argument("--lr", type=float, default=2.0e-4)
    args = parser.parse_args()
    train_stage1(epochs=args.epochs, seq_len=args.seq_len, lr=args.lr)
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(0)
