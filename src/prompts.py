"""
Canonical prompt templates and formatting utilities shared across:
- Stage 1: Pure Lean 4 Domain Adaptation / Pretraining
- Stage 2: Sketchpad SFT (<sketchpad>...</sketchpad> + ```lean ... ```)
- Stage 3: Multi-Round Per-Question GRPO on Hard Pure Lean Theorems
- Evaluation across all checkpoints
"""

from __future__ import annotations

from typing import Dict, List, Optional

SYSTEM_PROMPT_SKETCHPAD = (
    "You are an expert Lean 4 theorem prover working strictly in pure Lean 4 (zero Mathlib imports). "
    "Given pure Lean 4 definitions and a theorem signature ending with `:=`, first reason carefully "
    "step-by-step inside `<sketchpad>...</sketchpad>`: inspect the types and definitions, choose the "
    "right proof strategy (such as `intro`, `rcases`, `induction`, `rw`, `calc`, `apply`, `omega`, "
    "`Classical.em`, or local `have` helper lemmas), verify rewrite directions and base cases, and "
    "avoid Mathlib-only tactics (`ring`, `linarith`, `norm_num`, `tauto`). "
    "After `</sketchpad>`, output ONLY the Lean 4 proof body (starting with `by` or a proof term) "
    "inside a ```lean ... ``` block, with no `sorry`, `admit`, or `axiom`."
)


def format_problem_block(preamble: str, theorem_header: str) -> str:
    pre = preamble.strip()
    hdr = theorem_header.strip()
    if not hdr.endswith(":="):
        hdr += " :="
    if pre:
        return f"```lean\n{pre}\n\n{hdr}\n```"
    return f"```lean\n{hdr}\n```"


def build_user_prompt(preamble: str, theorem_header: str, warmup_hint: Optional[str] = None) -> str:
    block = format_problem_block(preamble, theorem_header)
    base = (
        "Prove the following pure Lean 4 theorem without Mathlib. "
        "Reason in `<sketchpad>...</sketchpad>` and then provide the proof body after `:=` in a ```lean``` block.\n\n"
        f"{block}"
    )
    if warmup_hint:
        base += f"\n\nHint for proof planning: {warmup_hint}"
    return base


def build_assistant_sketchpad_response(sketchpad: str, proof_body: str) -> str:
    return f"<sketchpad>\n{sketchpad.strip()}\n</sketchpad>\n```lean\n{proof_body.strip()}\n```"


def build_chat_messages(
    preamble: str,
    theorem_header: str,
    assistant_response: Optional[str] = None,
    warmup_hint: Optional[str] = None,
) -> List[Dict[str, str]]:
    msgs = [
        {"role": "system", "content": SYSTEM_PROMPT_SKETCHPAD},
        {"role": "user", "content": build_user_prompt(preamble, theorem_header, warmup_hint=warmup_hint)},
    ]
    if assistant_response is not None:
        msgs.append({"role": "assistant", "content": assistant_response})
    return msgs


def format_stage1_pure_lean_doc(preamble: str, theorem_header: str, proof_body: str, domain: str) -> str:
    """
    Format Stage 1 pure Lean training document as clean, self-contained pure Lean 4 source
    with module header comment, teaching pure Lean 4 declarations, typeclasses, inductive
    types, and core tactic/term proofs.
    """
    pre = preamble.strip()
    hdr = theorem_header.strip()
    if not hdr.endswith(":="):
        hdr += " :="
    body = proof_body.strip()
    header_comment = f"/- Pure Lean 4 Module ({domain}) — No Mathlib -/\n"
    if pre:
        return f"{header_comment}{pre}\n\n{hdr}\n{body}\n"
    return f"{header_comment}{hdr}\n{body}\n"
