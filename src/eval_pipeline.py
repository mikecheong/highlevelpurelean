"""
Unified Formal Lean 4.36 Benchmark Evaluator across all 4 pipeline checkpoints:
  0. Base Model (`Qwen/Qwen2.5-Coder-3B-Instruct`)
  1. Stage 1 Pure Lean 3B (`checkpoints/stage1_pure_lean_merged`)
  2. Stage 2 Sketchpad SFT 3B (`checkpoints/stage2_sketchpad_sft_merged`)
  3. Stage 3 GRPO Mastered 3B (`checkpoints/stage3_grpo_merged`)

Evaluates unhinted Lean-4.36-kernel-verified accuracy (Pass@1 mean accuracy,
Pass@k coverage, >=75% mastery rate, and `<sketchpad>` format adherence) on both:
  - The 15 Hard Pure Lean GRPO Questions (`data/stage3_hard_grpo.jsonl`)
  - The 12 Unseen Holdout Pure Lean Theorems (`data/eval_holdout.jsonl`)
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from typing import Any, Dict, List

import torch

from src.lean_verifier import verify_rollouts_parallel
from src.mps_lora_utils import (
    DEFAULT_BASE_MODEL,
    clear_mps_cache,
    get_device,
    load_causal_lm,
    load_tokenizer,
)
from src.prompts import build_chat_messages
from src.train_stage3_grpo import generate_group_rollouts


def load_jsonl(path: str) -> List[Dict[str, Any]]:
    rows: List[Dict[str, Any]] = []
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def evaluate_checkpoint_on_suite(
    model,
    tokenizer,
    questions: List[Dict[str, Any]],
    suite_name: str,
    group_size: int,
    device: str,
    temperature: float = 0.70,
    max_new_tokens: int = 1024,
) -> Dict[str, Any]:
    t0 = time.time()
    per_question: List[Dict[str, Any]] = []
    total_verified = 0
    total_rollouts = 0
    pass_any_count = 0
    mastery_75_count = 0
    sketchpad_count = 0

    for q in questions:
        msgs = build_chat_messages(q["preamble"], q["theorem_header"], warmup_hint=None)
        _, _, texts = generate_group_rollouts(
            model=model,
            tokenizer=tokenizer,
            messages=msgs,
            group_size=group_size,
            device=device,
            max_new_tokens=max_new_tokens,
            temperature=temperature,
            top_p=0.95,
        )
        ver = verify_rollouts_parallel(
            preamble=q["preamble"],
            theorem_header=q["theorem_header"],
            responses=texts,
            require_sketchpad_for_bonus=True,
            max_workers=group_size,
        )
        n_ok = sum(1 for v in ver if v.verified_correct)
        n_sk = sum(1 for v in ver if v.has_sketchpad)
        acc = n_ok / float(group_size)

        total_verified += n_ok
        total_rollouts += group_size
        sketchpad_count += n_sk
        if n_ok > 0:
            pass_any_count += 1
        if acc >= 0.75:
            mastery_75_count += 1

        per_question.append(
            {
                "id": q["id"],
                "domain": q["domain"],
                "verified": n_ok,
                "group_size": group_size,
                "accuracy": round(acc, 4),
                "pass_at_k": n_ok > 0,
                "mastered_75": acc >= 0.75,
                "sketchpad_rate": round(n_sk / float(group_size), 4),
            }
        )
        if torch.backends.mps.is_available():
            torch.mps.empty_cache()

    n_q = max(1, len(questions))
    res = {
        "suite": suite_name,
        "num_questions": len(questions),
        "group_size": group_size,
        "mean_accuracy_pass_at_1": round(total_verified / max(1, total_rollouts), 4),
        "pass_at_k_rate": round(pass_any_count / n_q, 4),
        "mastery_75_rate": round(mastery_75_count / n_q, 4),
        "mastery_75_count": mastery_75_count,
        "sketchpad_adherence": round(sketchpad_count / max(1, total_rollouts), 4),
        "elapsed_sec": round(time.time() - t0, 2),
        "per_question": per_question,
    }
    print(
        f"  [{suite_name}] acc(Pass@1)={res['mean_accuracy_pass_at_1']*100:.1f}%, "
        f"Pass@{group_size}={res['pass_at_k_rate']*100:.1f}%, "
        f">=75%_mastered={mastery_75_count}/{len(questions)} ({res['mastery_75_rate']*100:.1f}%), "
        f"sketchpad={res['sketchpad_adherence']*100:.1f}% ({res['elapsed_sec']}s)",
        flush=True,
    )
    return res


def run_all_evaluations(
    hard_path: str = "data/stage3_hard_grpo.jsonl",
    holdout_path: str = "data/eval_holdout.jsonl",
    out_path: str = "logs/final_evaluation.json",
    hard_group_size: int = 8,
    holdout_group_size: int = 4,
) -> Dict[str, Any]:
    device = get_device()
    hard_qs = load_jsonl(hard_path)
    holdout_qs = load_jsonl(holdout_path)

    checkpoints = [
        ("0_base_qwen25_coder_3b", DEFAULT_BASE_MODEL),
        ("1_stage1_pure_lean_3b", "checkpoints/stage1_pure_lean_merged"),
        ("2_stage2_sketchpad_sft_3b", "checkpoints/stage2_sketchpad_sft_merged"),
        ("3_stage3_grpo_mastered_3b", "checkpoints/stage3_grpo_merged"),
    ]

    all_results: Dict[str, Any] = {}
    for label, ckpt_path in checkpoints:
        if ckpt_path != DEFAULT_BASE_MODEL and not os.path.isdir(ckpt_path):
            print(f"[Eval] Skipping {label} (missing {ckpt_path})", flush=True)
            continue
        print(f"\n=== Evaluating Checkpoint: {label} ({ckpt_path}) ===", flush=True)
        tok = load_tokenizer(ckpt_path)
        model = load_causal_lm(ckpt_path, device=device, dtype=torch.bfloat16, gradient_checkpointing=False)

        hard_res = evaluate_checkpoint_on_suite(
            model, tok, hard_qs, "hard_15_grpo", group_size=hard_group_size, device=device
        )
        hold_res = evaluate_checkpoint_on_suite(
            model, tok, holdout_qs, "unseen_12_holdout", group_size=holdout_group_size, device=device
        )
        all_results[label] = {
            "checkpoint": ckpt_path,
            "hard_15_grpo": hard_res,
            "unseen_12_holdout": hold_res,
        }

        del model
        clear_mps_cache()

        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(all_results, f, indent=2)

    print(f"\n[Eval] Saved complete multi-stage formal evaluation to {out_path}", flush=True)
    return all_results


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--hard-k", type=int, default=8)
    parser.add_argument("--holdout-k", type=int, default=4)
    args = parser.parse_args()
    run_all_evaluations(hard_group_size=args.hard_k, holdout_group_size=args.holdout_k)
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(0)
