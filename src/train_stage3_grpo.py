"""
Stage 3: Per-Question Multi-Round GRPO on Hard Pure Lean 4 Questions.

For each hard question in `data/stage3_hard_grpo.jsonl`:
  - Iterates over rounds r = 1, 2, ..., max_rounds:
    1. Samples G = 8 unhinted `<sketchpad>` + Lean 4 proof rollouts on MPS.
    2. Verifies all 8 rollouts in parallel with the Lean 4.36 kernel (`#print axioms`).
    3. Checks strict unhinted pass rate: if `verified_count / G >= 0.75` (>= 6/8),
       records verified proofs in the anti-forgetting mastery buffer and advances
       immediately to the next hard question!
    4. Otherwise computes Group Relative Policy Optimization (GRPO) advantages using
       dense compiler-feedback shaped rewards (plus adaptive temperature / sublemma
       warmup exploration if stuck at 0% unhinted), updates the LoRA policy with
       clipped surrogate objective + unbiased KL penalty against Stage 2 SFT
       (`disable_adapter()`) + lightweight mastery replay, and repeats the next round!

Merges the final mastered LoRA adapter into `checkpoints/stage3_grpo_merged`.
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
import time
from typing import Any, Dict, List, Optional, Tuple

import torch

from src.lean_verifier import VerificationResult, verify_rollouts_parallel
from src.mps_lora_utils import (
    attach_lora,
    clear_mps_cache,
    compute_chunked_lm_loss,
    compute_completion_token_logprobs,
    compute_grpo_single_seq_loss,
    get_device,
    load_causal_lm,
    load_tokenizer,
    merge_and_save_checkpoint,
    render_chat_ids,
)
from src.prompts import build_assistant_sketchpad_response, build_chat_messages


def generate_group_rollouts(
    model,
    tokenizer,
    messages: List[Dict[str, str]],
    group_size: int,
    device: str,
    max_new_tokens: int = 448,
    temperature: float = 0.75,
    top_p: float = 0.95,
) -> Tuple[List[int], List[List[int]], List[str]]:
    """
    Generate `group_size` completions in one batched KV-cached forward pass on MPS.
    Returns `(prompt_ids, completion_id_lists, decoded_texts)`.
    """
    was_gc = getattr(model, "is_gradient_checkpointing", False)
    if was_gc and hasattr(model, "gradient_checkpointing_disable"):
        model.gradient_checkpointing_disable()
    model.eval()
    model.config.use_cache = True

    prompt_ids: List[int] = render_chat_ids(tokenizer, messages, add_generation_prompt=True)
    inp = torch.tensor([prompt_ids] * group_size, dtype=torch.long, device=device)
    attn = torch.ones_like(inp)

    with torch.no_grad():
        out = model.generate(
            input_ids=inp,
            attention_mask=attn,
            max_new_tokens=max_new_tokens,
            do_sample=True,
            temperature=temperature,
            top_p=top_p,
            pad_token_id=tokenizer.pad_token_id,
            eos_token_id=tokenizer.eos_token_id,
            use_cache=True,
        )

    prompt_len = len(prompt_ids)
    eos_id = tokenizer.eos_token_id
    pad_id = tokenizer.pad_token_id

    comp_ids_list: List[List[int]] = []
    texts: List[str] = []

    for row in out[:, prompt_len:].tolist():
        # Trim after first EOS token
        trimmed: List[int] = []
        for tid in row:
            if tid == eos_id:
                trimmed.append(tid)
                break
            if tid == pad_id and eos_id != pad_id:
                break
            trimmed.append(tid)
        if not trimmed:
            trimmed = [eos_id]
        comp_ids_list.append(trimmed)
        texts.append(tokenizer.decode(trimmed, skip_special_tokens=True))

    if was_gc and hasattr(model, "gradient_checkpointing_enable"):
        model.gradient_checkpointing_enable(
            gradient_checkpointing_kwargs={"use_reentrant": False}
        )
    model.config.use_cache = False
    return prompt_ids, comp_ids_list, texts


def pad_rollout_pair(
    prompt_ids: List[int],
    comp_batch: List[List[int]],
    pad_id: int,
    device: str,
) -> Tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """
    Build `(input_ids, attention_mask, completion_mask)` for a microbatch of completions
    sharing `prompt_ids` of length `P`.
    `completion_mask` has shape `(B, max_comp_len)` with `1.0` on valid completion tokens.
    """
    plen = len(prompt_ids)
    max_clen = max(len(c) for c in comp_batch)
    bsz = len(comp_batch)
    total_len = plen + max_clen

    input_ids = torch.full((bsz, total_len), pad_id, dtype=torch.long, device=device)
    attn_mask = torch.zeros((bsz, total_len), dtype=torch.long, device=device)
    comp_mask = torch.zeros((bsz, max_clen), dtype=torch.float32, device=device)

    p_tensor = torch.tensor(prompt_ids, dtype=torch.long, device=device)
    for i, comp in enumerate(comp_batch):
        clen = len(comp)
        input_ids[i, :plen] = p_tensor
        input_ids[i, plen : plen + clen] = torch.tensor(comp, dtype=torch.long, device=device)
        attn_mask[i, : plen + clen] = 1
        comp_mask[i, :clen] = 1.0

    return input_ids, attn_mask, comp_mask


def grpo_update_step(
    model,
    optimizer: torch.optim.Optimizer,
    trainable_params: List[torch.nn.Parameter],
    prompt_ids: List[int],
    comp_ids_list: List[List[int]],
    rewards: List[float],
    pad_id: int,
    device: str,
    mastery_buffer: List[Tuple[List[int], List[int]]],
    rng: random.Random,
    micro_batch_size: int = 2,
    inner_epochs: int = 2,
    clip_eps: float = 0.2,
    kl_beta: float = 0.02,
    replay_weight: float = 0.15,
) -> Dict[str, float]:
    """
    Execute GRPO policy gradient update on a group of `G` completions conditioned on
    the UNHINTED `prompt_ids`, using `model.disable_adapter()` for exact zero-memory
    reference log-probabilities and optional lightweight mastery replay.
    """
    r_tensor = torch.tensor(rewards, dtype=torch.float32)
    r_mean = float(r_tensor.mean().item())
    r_std = float(r_tensor.std(unbiased=False).item())
    if r_std < 1e-5:
        return {"skipped_zero_var": 1.0, "policy_loss": 0.0, "kl": 0.0, "reward_std": r_std}

    advantages = ((r_tensor - r_mean) / (r_std + 1e-5)).tolist()
    plen = len(prompt_ids)

    # Precompute `old_logprobs` and `ref_logprobs` per rollout (`micro_batch_size=1`, zero swap)
    cached_rollouts = []
    model.eval()
    total_valid_tokens = float(sum(len(c) for c in comp_ids_list))
    total_valid_tokens = max(1.0, total_valid_tokens)

    for c_ids, adv_val in zip(comp_ids_list, advantages):
        inp, attn, _ = pad_rollout_pair(prompt_ids, [c_ids], pad_id=pad_id, device=device)
        with torch.no_grad():
            old_lp = compute_completion_token_logprobs(model, inp, attn, prompt_len=plen).detach()
            with model.disable_adapter():
                ref_lp = compute_completion_token_logprobs(model, inp, attn, prompt_len=plen).detach()
        cached_rollouts.append((inp, attn, float(adv_val), old_lp, ref_lp))

    model.train()
    last_pg_loss = 0.0
    last_kl = 0.0

    for _ in range(inner_epochs):
        optimizer.zero_grad()
        agg_pg = 0.0
        agg_kl = 0.0

        for inp, attn, adv_val, old_lp, ref_lp in cached_rollouts:
            seq_loss, pg_s, kl_s = compute_grpo_single_seq_loss(
                model=model,
                input_ids=inp,
                attention_mask=attn,
                prompt_len=plen,
                advantage=adv_val,
                old_lp=old_lp,
                ref_lp=ref_lp,
                norm_tokens=total_valid_tokens,
                clip_eps=clip_eps,
                kl_beta=kl_beta,
            )
            seq_loss.backward()
            agg_pg += pg_s
            agg_kl += kl_s

        # Lightweight anti-forgetting anchor on 1 mastered rollout from earlier questions
        if mastery_buffer and replay_weight > 0.0:
            m_inp_list, m_lbl_list = rng.choice(mastery_buffer)
            m_inp = torch.tensor([m_inp_list], dtype=torch.long, device=device)
            m_attn = torch.ones_like(m_inp)
            m_lbl = torch.tensor([m_lbl_list], dtype=torch.long, device=device)
            r_loss, n_rtok = compute_chunked_lm_loss(model, m_inp, m_attn, m_lbl, token_chunk_size=128)
            if n_rtok > 0:
                (replay_weight * r_loss).backward()

        torch.nn.utils.clip_grad_norm_(trainable_params, max_norm=1.0)
        optimizer.step()
        if torch.backends.mps.is_available():
            torch.mps.empty_cache()
        last_pg_loss = agg_pg
        last_kl = agg_kl

    return {
        "skipped_zero_var": 0.0,
        "policy_loss": round(last_pg_loss, 5),
        "kl": round(last_kl, 5),
        "reward_mean": round(r_mean, 4),
        "reward_std": round(r_std, 4),
    }


def train_stage3_grpo(
    stage2_model_dir: str = "checkpoints/stage2_sketchpad_sft_merged",
    questions_path: str = "data/stage3_hard_grpo.jsonl",
    merged_out_dir: str = "checkpoints/stage3_grpo_merged",
    adapter_out_dir: str = "checkpoints/stage3_grpo_lora",
    metrics_path: str = "logs/stage3_grpo_metrics.json",
    group_size: int = 8,
    target_accuracy: float = 0.75,
    max_rounds_per_question: int = 25,
    max_new_tokens: int = 1024,
    lr: float = 5.0e-5,
    lora_r: int = 16,
    lora_alpha: int = 32,
    kl_beta: float = 0.015,
    seed: int = 2026,
    resume_unmastered: bool = False,
) -> Dict[str, Any]:
    t0 = time.time()
    torch.manual_seed(seed)
    rng = random.Random(seed)
    device = get_device()

    questions: List[Dict[str, Any]] = []
    with open(questions_path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                questions.append(json.loads(line))

    print(
        f"[Stage 3 GRPO] Loaded {len(questions)} hard pure Lean questions. "
        f"Target mastery >= {target_accuracy*100:.0f}% ({math.ceil_equiv(group_size, target_accuracy)}/{group_size}) "
        f"unhinted Lean-verified per question (max_rounds={max_rounds_per_question}).",
        flush=True,
    )

    source_dir = merged_out_dir if (resume_unmastered and os.path.isdir(merged_out_dir)) else stage2_model_dir
    tokenizer = load_tokenizer(source_dir)
    pad_id = tokenizer.pad_token_id
    eos_id = tokenizer.eos_token_id

    base = load_causal_lm(source_dir, device=device, dtype=torch.bfloat16, gradient_checkpointing=False)
    model = attach_lora(base, r=lora_r, lora_alpha=lora_alpha, lora_dropout=0.0, device=device)

    trainable_params = [p for p in model.parameters() if p.requires_grad]
    optimizer = torch.optim.AdamW(trainable_params, lr=lr, weight_decay=0.0)

    mastery_buffer: List[Tuple[List[int], List[int]]] = []
    prior_map: Dict[str, Dict[str, Any]] = {}
    if resume_unmastered and os.path.exists(metrics_path):
        prev_data = json.load(open(metrics_path, "r", encoding="utf-8"))
        for pq in prev_data.get("questions", []):
            if pq.get("graduated"):
                prior_map[pq["id"]] = pq
        # Seed mastery_buffer with reference proofs of already-mastered questions for anti-forgetting
        for q in questions:
            if q["id"] in prior_map and "reference_sketchpad" in q and "reference_proof" in q:
                p_ids = render_chat_ids(tokenizer, build_chat_messages(q["preamble"], q["theorem_header"]), add_generation_prompt=True)
                c_ids = tokenizer.encode(build_assistant_sketchpad_response(q["reference_sketchpad"], q["reference_proof"]), add_special_tokens=False) + [eos_id]
                mastery_buffer.append((p_ids + c_ids, [-100] * len(p_ids) + c_ids))
        print(f"[Stage 3 GRPO] Resuming from {source_dir} with {len(prior_map)} already-mastered questions protected in replay buffer.", flush=True)

    question_reports: List[Dict[str, Any]] = []
    total_rounds_all = 0
    mastered_count = 0

    for q_idx, q in enumerate(questions):
        qid = q["id"]
        if qid in prior_map:
            prev_q = prior_map[qid]
            question_reports.append(prev_q)
            total_rounds_all += int(prev_q.get("rounds_used", 0))
            mastered_count += 1
            print(f"[Skipping already mastered] {qid} ({prev_q['final_accuracy']*100:.1f}% in {prev_q['rounds_used']} rounds)", flush=True)
            continue
        preamble = q["preamble"]
        thm_header = q["theorem_header"]
        warmup_hint = q.get("warmup_hint", "")

        unhinted_msgs = build_chat_messages(preamble, thm_header, warmup_hint=None)
        hinted_msgs = build_chat_messages(preamble, thm_header, warmup_hint=warmup_hint) if warmup_hint else unhinted_msgs

        print(f"\n=== [Question {q_idx+1}/{len(questions)}] {qid}: {q['title']} ===", flush=True)

        q_rounds: List[Dict[str, Any]] = []
        q_self_verified: List[Tuple[List[int], float]] = []
        zero_streak = 0
        graduated = False
        best_acc = 0.0
        q_start = time.time()

        for rnd in range(1, max_rounds_per_question + 1):
            r_t0 = time.time()
            total_rounds_all += 1

            # Adaptive sampling temperature based on recent progress
            if zero_streak == 0:
                temp = 0.65 if best_acc >= 0.50 else 0.75
            elif zero_streak == 1:
                temp = 0.85
            else:
                temp = min(1.0, 0.90 + 0.03 * (zero_streak - 2))

            prompt_ids, comp_ids_list, texts = generate_group_rollouts(
                model=model,
                tokenizer=tokenizer,
                messages=unhinted_msgs,
                group_size=group_size,
                device=device,
                max_new_tokens=max_new_tokens,
                temperature=temp,
                top_p=0.95,
            )

            ver_results: List[VerificationResult] = verify_rollouts_parallel(
                preamble=preamble,
                theorem_header=thm_header,
                responses=texts,
                require_sketchpad_for_bonus=True,
                max_workers=group_size,
            )

            n_verified = sum(1 for v in ver_results if v.verified_correct)
            acc = n_verified / float(group_size)
            best_acc = max(best_acc, acc)
            rewards = [v.shaped_reward for v in ver_results]

            round_info: Dict[str, Any] = {
                "round": rnd,
                "temperature": round(temp, 2),
                "verified_correct": n_verified,
                "group_size": group_size,
                "accuracy": round(acc, 4),
                "mean_shaped_reward": round(sum(rewards) / len(rewards), 4),
                "max_shaped_reward": round(max(rewards), 4),
                "sample_errors": [v.error_summary for v in ver_results if not v.verified_correct][:2],
            }

            # Harvest any genuine unhinted verified rollouts into mastery buffer (up to 2 per question)
            added_for_q = 0
            for c_ids, v in zip(comp_ids_list, ver_results):
                if v.verified_correct:
                    if len(q_self_verified) < 4:
                        q_self_verified.append((c_ids, v.shaped_reward))
                    if added_for_q < 2:
                        full_seq = prompt_ids + c_ids
                        lbl_seq = [-100] * len(prompt_ids) + c_ids
                        mastery_buffer.append((full_seq, lbl_seq))
                        added_for_q += 1

            # STRICT >= 75% UNHINTED MASTERY CHECK!
            if acc >= target_accuracy:
                graduated = True
                round_info["graduated"] = True
                round_info["round_sec"] = round(time.time() - r_t0, 2)
                q_rounds.append(round_info)
                print(
                    f"  [Round {rnd:02d}] MASTERED! Unhinted verified = {n_verified}/{group_size} "
                    f"({acc*100:.1f}% >= {target_accuracy*100:.0f}%) in {round_info['round_sec']}s!",
                    flush=True,
                )
                break

            if n_verified == 0:
                zero_streak += 1
            else:
                zero_streak = 0

            # Adaptive sublemma warmup / exploration ladder when stuck at 0% unhinted
            train_comp_ids = list(comp_ids_list)
            train_rewards = list(rewards)
            warmup_mode = "none"

            if n_verified == 0 and q_self_verified:
                # Replay the model's OWN earlier unhinted verified rollout for this question
                sc_ids, sc_rew = rng.choice(q_self_verified)
                worst_idx = min(range(len(train_rewards)), key=lambda idx: train_rewards[idx])
                train_comp_ids[worst_idx] = sc_ids
                train_rewards[worst_idx] = sc_rew
                warmup_mode = "self_verified_replay"
            elif n_verified == 0 and zero_streak >= 2:
                h_pass = 0
                if warmup_hint and zero_streak == 2:
                    # Tier 2: Sample 4 hint-guided rollouts and evaluate them on the UNHINTED prompt
                    _, h_comp_ids, h_texts = generate_group_rollouts(
                        model=model,
                        tokenizer=tokenizer,
                        messages=hinted_msgs,
                        group_size=4,
                        device=device,
                        max_new_tokens=max_new_tokens,
                        temperature=0.80,
                        top_p=0.95,
                    )
                    h_ver = verify_rollouts_parallel(
                        preamble=preamble,
                        theorem_header=thm_header,
                        responses=h_texts,
                        require_sketchpad_for_bonus=True,
                        max_workers=4,
                    )
                    h_pass = sum(1 for v in h_ver if v.verified_correct)
                    warmup_mode = f"hint_rollouts(pass={h_pass}/4)"
                    if h_pass > 0:
                        order = sorted(range(len(train_rewards)), key=lambda idx: train_rewards[idx])
                        for rep_slot, hc, hv in zip(order[:4], h_comp_ids, h_ver):
                            train_comp_ids[rep_slot] = hc
                            train_rewards[rep_slot] = hv.shaped_reward

                if h_pass == 0 and zero_streak >= 3 and "reference_sketchpad" in q and "reference_proof" in q:
                    # Tier 3: Contrastive sublemma curriculum trajectory against failed rollouts
                    ref_text = build_assistant_sketchpad_response(q["reference_sketchpad"], q["reference_proof"])
                    ref_ids = tokenizer.encode(ref_text, add_special_tokens=False) + [eos_id]
                    if len(ref_ids) <= max_new_tokens + 256:
                        n_inject = 2 if zero_streak >= 5 else 1
                        order = sorted(range(len(train_rewards)), key=lambda idx: train_rewards[idx])
                        for slot in order[:n_inject]:
                            train_comp_ids[slot] = ref_ids
                            train_rewards[slot] = 1.08
                        warmup_mode = f"contrastive_curriculum_{n_inject}of{group_size}"

            upd_stats = grpo_update_step(
                model=model,
                optimizer=optimizer,
                trainable_params=trainable_params,
                prompt_ids=prompt_ids,
                comp_ids_list=train_comp_ids,
                rewards=train_rewards,
                pad_id=pad_id,
                device=device,
                mastery_buffer=mastery_buffer[:-added_for_q] if added_for_q > 0 else mastery_buffer,
                rng=rng,
                micro_batch_size=2,
                inner_epochs=2,
                clip_eps=0.2,
                kl_beta=kl_beta,
                replay_weight=0.15,
            )

            round_info["graduated"] = False
            round_info["warmup_mode"] = warmup_mode
            round_info["update"] = upd_stats
            round_info["round_sec"] = round(time.time() - r_t0, 2)
            q_rounds.append(round_info)

            print(
                f"  [Round {rnd:02d}] unhinted={n_verified}/{group_size} ({acc*100:.1f}%), "
                f"mean_r={round_info['mean_shaped_reward']:.3f}, warmup={warmup_mode}, "
                f"pg={upd_stats.get('policy_loss', 0.0):.4f}, kl={upd_stats.get('kl', 0.0):.4f}, "
                f"t={round_info['round_sec']}s",
                flush=True,
            )

        if graduated:
            mastered_count += 1
        else:
            print(
                f"  [Safety Cap Reached] {qid} hit max_rounds={max_rounds_per_question} "
                f"(best unhinted acc={best_acc*100:.1f}%).",
                flush=True,
            )

        q_rep = {
            "id": qid,
            "domain": q["domain"],
            "title": q["title"],
            "graduated": graduated,
            "rounds_used": len(q_rounds),
            "initial_accuracy": q_rounds[0]["accuracy"],
            "final_accuracy": q_rounds[-1]["accuracy"],
            "best_accuracy": best_acc,
            "elapsed_sec": round(time.time() - q_start, 2),
            "rounds": q_rounds,
        }
        question_reports.append(q_rep)

        # Save incremental progress after every question
        os.makedirs(os.path.dirname(metrics_path), exist_ok=True)
        with open(metrics_path, "w", encoding="utf-8") as f:
            json.dump(
                {
                    "stage": "stage3_grpo_in_progress",
                    "completed_questions": len(question_reports),
                    "total_questions": len(questions),
                    "mastered_so_far": mastered_count,
                    "total_rounds_so_far": total_rounds_all,
                    "questions": question_reports,
                },
                f,
                indent=2,
            )
        clear_mps_cache()

    print(f"\n[Stage 3 GRPO] Merging mastered GRPO adapter into {merged_out_dir} ...", flush=True)
    merge_and_save_checkpoint(model, tokenizer, save_dir=merged_out_dir, adapter_dir=adapter_out_dir)

    summary = {
        "stage": "stage3_grpo",
        "source_model": stage2_model_dir,
        "merged_checkpoint": merged_out_dir,
        "adapter_checkpoint": adapter_out_dir,
        "group_size": group_size,
        "target_accuracy": target_accuracy,
        "max_rounds_per_question": max_rounds_per_question,
        "total_questions": len(questions),
        "mastered_questions": mastered_count,
        "mastery_rate": round(mastered_count / max(1, len(questions)), 4),
        "total_grpo_rounds": total_rounds_all,
        "avg_rounds_per_question": round(total_rounds_all / max(1, len(questions)), 2),
        "elapsed_sec": round(time.time() - t0, 2),
        "questions": question_reports,
    }
    with open(metrics_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2)

    print(
        f"[Stage 3 GRPO] Done in {summary['elapsed_sec']}s! "
        f"Mastered {mastered_count}/{len(questions)} hard questions (>=75% unhinted correct) "
        f"over {total_rounds_all} total rounds.",
        flush=True,
    )
    clear_mps_cache()
    return summary


def math_ceil_equiv(group_size: int, target_acc: float) -> int:
    import math as _m
    return int(_m.ceil(group_size * target_acc - 1e-9))


# Attach helper alias used in log string
class _MathHelper:
    ceil_equiv = staticmethod(math_ceil_equiv)


math = _MathHelper()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--group-size", type=int, default=8)
    parser.add_argument("--target-acc", type=float, default=0.75)
    parser.add_argument("--max-rounds", type=int, default=25)
    parser.add_argument("--max-new-tokens", type=int, default=1024)
    parser.add_argument("--lr", type=float, default=5.0e-5)
    parser.add_argument("--resume-unmastered", action="store_true")
    args = parser.parse_args()
    train_stage3_grpo(
        group_size=args.group_size,
        target_accuracy=args.target_acc,
        max_rounds_per_question=args.max_rounds,
        max_new_tokens=args.max_new_tokens,
        lr=args.lr,
        resume_unmastered=args.resume_unmastered,
    )
    sys.stdout.flush()
    sys.stderr.flush()
    os._exit(0)
