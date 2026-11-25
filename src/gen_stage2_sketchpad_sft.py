"""
Stage 2 Sketchpad SFT Dataset Generator (~2,100+ Lean-4.36-verified examples).
Generates rich `<sketchpad>...</sketchpad>` step-by-step reasoning traces paired
with clean pure Lean 4 proofs across:
- Semirings, Rings, Product Groups, Subgroup/Kernel/Stabilizer Predicates
- Bounded Lattices, Heyting Algebras, Fixed Points & Galois Residuation
- Transitive/Reflexive-Transitive Closures, Simulations & Set-Predicate Laws
- Higher-Order Logic, Cantor Diagonalization, Option/Prod/Sum Monads & Retractions
- Tail-Recursive Accumulator Generalization, Folds/Filters & Stack-Machine Compilers
- Modular Congruence, Recurrences, Nonlinear Nat Identities & Divisibility
Plus multi-perspective sketchpad reasoning (dead-end recovery, tactic-state tracking,
auxiliary `have` lemma synthesis, and `calc` blueprints).
"""

from __future__ import annotations

import json
import os
import random
import time
from dataclasses import asdict, dataclass
from typing import Dict, List, Tuple

from src.lean_verifier import extract_theorem_name, verify_snippets_batch
from src.prompts import (
    build_assistant_sketchpad_response,
    build_chat_messages,
)


@dataclass
class SketchpadSFTItem:
    id: str
    domain: str
    style: str
    difficulty: int
    preamble: str
    theorem_header: str
    sketchpad: str
    proof_body: str
    assistant_response: str
    messages: List[Dict[str, str]]
    full_lean: str

    def to_dict(self) -> Dict:
        return asdict(self)


def build_sft_item(
    idx: int,
    domain: str,
    style: str,
    difficulty: int,
    preamble: str,
    theorem_header: str,
    sketchpad: str,
    proof_body: str,
) -> SketchpadSFTItem:
    pre = preamble.strip()
    hdr = theorem_header.strip()
    if not hdr.endswith(":="):
        hdr += " :="
    body = proof_body.strip()
    sk = sketchpad.strip()
    resp = build_assistant_sketchpad_response(sk, body)
    msgs = build_chat_messages(pre, hdr, assistant_response=resp)
    full = (pre + "\n\n" if pre else "") + f"{hdr}\n{body}"
    return SketchpadSFTItem(
        id=f"s2_{domain}_{idx:04d}",
        domain=domain,
        style=style,
        difficulty=difficulty,
        preamble=pre,
        theorem_header=hdr,
        sketchpad=sk,
        proof_body=body,
        assistant_response=resp,
        messages=msgs,
        full_lean=full,
    )


def render_sketchpad_style(
    style_idx: int,
    thm_header: str,
    domain: str,
    steps: List[str],
    pitfall: str = "",
) -> Tuple[str, str]:
    """Render diverse, natural scratchpad reasoning across 5 cognitive styles."""
    thm_name = extract_theorem_name(thm_header)
    goal_rhs = thm_header.split(":", 1)[-1].rsplit(":=", 1)[0].strip() if ":" in thm_header else thm_header

    pitfall_default = (
        "Remember: we are in pure Lean 4 with zero Mathlib imports, so tactics like `ring`, "
        "`linarith`, `norm_num`, or `tauto` do not exist; stick to core tactics (`intro`, `rcases`, "
        "`induction`, `rw`, `simp`, `calc`, `apply`, `omega`, `Classical.em`)."
    )
    warn = pitfall if pitfall else pitfall_default

    mode = style_idx % 5
    if mode == 0:
        # Analytical plan
        lines = [
            f"Target theorem `{thm_name}` ({domain}): we need to prove `{goal_rhs}`.",
            "Plan:",
        ]
        for k, s in enumerate(steps, 1):
            lines.append(f"{k}. {s}")
        lines.append(f"Check: {warn}")
        return "analytical_plan", "\n".join(lines)
    elif mode == 1:
        # Dead-end & self-correction trace
        lines = [
            f"Goal analysis for `{thm_name}`: `{goal_rhs}`.",
            f"Initial check: {warn}",
            "Let's trace a sound step-by-step derivation:",
        ]
        for s in steps:
            lines.append(f"- {s}")
        lines.append("All hypotheses and rewrite orientations align cleanly; ready to write the Lean 4 proof.")
        return "self_correcting", "\n".join(lines)
    elif mode == 2:
        # Tactic-state mental simulation
        lines = [
            f"Inspecting `{thm_name}` with target `{goal_rhs}`.",
            "Mental tactic trace:",
        ]
        for s in steps:
            lines.append(f"  ⊢ {s}")
        lines.append(f"Sanity check: no `sorry` or external lemmas needed. ({warn})")
        return "tactic_trace", "\n".join(lines)
    elif mode == 3:
        # Subgoal / lemma decomposition
        lines = [
            f"Decomposing `{thm_name}`:",
            f"Main claim: `{goal_rhs}`.",
            "Key proof obligations:",
        ]
        for s in steps:
            lines.append(f"* {s}")
        lines.append("Each obligation reduces to core Lean 4 axioms/definitions in the preamble.")
        return "subgoal_tree", "\n".join(lines)
    else:
        # Concise mathematical scratchpad
        joined = " ".join(steps)
        txt = (
            f"We prove `{goal_rhs}` in pure Lean 4. "
            f"{joined} "
            f"Note: {warn}"
        )
        return "concise_scratchpad", txt


# ---------------------------------------------------------------------------
# Family S2-1: Semirings, Rings, Direct Product Groups & Subgroup Predicates
# ---------------------------------------------------------------------------

RING_PREAMBLE = """\
class PureRing (R : Type) where
  add : R → R → R
  zero : R
  neg : R → R
  mul : R → R → R
  one : R
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  zero_add : ∀ a : R, add zero a = a
  add_zero : ∀ a : R, add a zero = a
  neg_add : ∀ a : R, add (neg a) a = zero
  add_neg : ∀ a : R, add a (neg a) = zero
  add_comm : ∀ a b : R, add a b = add b a
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : R, mul one a = a
  mul_one : ∀ a : R, mul a one = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)"""

SUBGROUP_PREAMBLE = """\
class PureGrp (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

structure IsSubgroup {G : Type} [PureGrp G] (S : G → Prop) : Prop where
  one_mem : S PureGrp.one
  mul_mem : ∀ {a b}, S a → S b → S (PureGrp.mul a b)
  inv_mem : ∀ {a}, S a → S (PureGrp.inv a)"""


def gen_s2_algebra(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "algebra", steps, pitfall)
        out.append(build_sft_item(idx, "algebra", st, diff, pre, hdr, sk, body))
        idx += 1

    r_vars = [
        ("a", "b", "c"),
        ("x", "y", "z"),
        ("r", "s", "t"),
        ("u", "v", "w"),
        ("p", "q", "d"),
        ("m", "n", "k"),
        ("a1", "a2", "a3"),
        ("x1", "x2", "x3"),
        ("c1", "c2", "c3"),
        ("e1", "e2", "e3"),
    ]
    for i, (a, b, c) in enumerate(r_vars):
        emit(
            2,
            RING_PREAMBLE,
            f"theorem ring_add_left_cancel_{i} {{R : Type}} [PureRing R] ({a} {b} {c} : R) "
            f"(h : PureRing.add {a} {b} = PureRing.add {a} {c}) : {b} = {c} :=",
            [
                f"Apply `PureRing.add (PureRing.neg {a})` to both sides of `h` via `congrArg`.",
                f"Reassociate `add (neg {a}) (add {a} _)` leftward using `← PureRing.add_assoc`.",
                f"Simplify `add (neg {a}) {a} = zero` and `add zero _ = _` via `neg_add` and `zero_add`.",
            ],
            "Do not use `linarith` or `ring`; `PureRing` is a custom typeclass so we rewrite explicitly with its projections.",
            f"by\n"
            f"  have h1 := congrArg (PureRing.add (PureRing.neg {a})) h\n"
            f"  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h1\n"
            f"  exact h1",
        )
        emit(
            3,
            RING_PREAMBLE,
            f"theorem ring_mul_zero_{i} {{R : Type}} [PureRing R] ({a} : R) : "
            f"PureRing.mul {a} PureRing.zero = PureRing.zero :=",
            [
                f"Key trick in ring theory: show `add (mul {a} zero) (mul {a} zero) = add (mul {a} zero) zero`.",
                f"On the LHS, factor `{a}` via `← PureRing.left_distrib` and simplify `add zero zero = zero`.",
                f"On the RHS, `add (mul {a} zero) zero = mul {a} zero` by `add_zero`.",
                f"Now cancel `mul {a} zero` on the left by adding `neg (mul {a} zero)` on the left!",
            ],
            "Direct `simp` cannot prove `a * 0 = 0` from raw ring axioms without factoring `0 = 0 + 0` and left-canceling.",
            f"by\n"
            f"  have h1 : PureRing.add (PureRing.mul {a} PureRing.zero) (PureRing.mul {a} PureRing.zero) = "
            f"PureRing.add (PureRing.mul {a} PureRing.zero) PureRing.zero := by\n"
            f"    rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]\n"
            f"  have h2 := congrArg (PureRing.add (PureRing.neg (PureRing.mul {a} PureRing.zero))) h1\n"
            f"  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h2\n"
            f"  exact h2",
        )
        emit(
            3,
            RING_PREAMBLE,
            f"theorem ring_zero_mul_{i} {{R : Type}} [PureRing R] ({a} : R) : "
            f"PureRing.mul PureRing.zero {a} = PureRing.zero :=",
            [
                f"Symmetrically to `mul_zero`, consider `add (mul zero {a}) (mul zero {a})`.",
                f"Collapse with `← PureRing.right_distrib` and `PureRing.zero_add`.",
                f"Cancel `mul zero {a}` on the left using `neg (mul zero {a})`.",
            ],
            "Use `right_distrib` (not `left_distrib`) since `zero` is the left factor.",
            f"by\n"
            f"  have h1 : PureRing.add (PureRing.mul PureRing.zero {a}) (PureRing.mul PureRing.zero {a}) = "
            f"PureRing.add (PureRing.mul PureRing.zero {a}) PureRing.zero := by\n"
            f"    rw [← PureRing.right_distrib, PureRing.zero_add, PureRing.add_zero]\n"
            f"  have h2 := congrArg (PureRing.add (PureRing.neg (PureRing.mul PureRing.zero {a}))) h1\n"
            f"  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h2\n"
            f"  exact h2",
        )
        emit(
            3,
            RING_PREAMBLE,
            f"theorem ring_neg_eq_of_add_zero_{i} {{R : Type}} [PureRing R] ({a} {b} : R) "
            f"(h : PureRing.add {a} {b} = PureRing.zero) : {b} = PureRing.neg {a} :=",
            [
                f"Add `neg {a}` on the left of `add {a} {b} = zero`.",
                f"LHS simplifies via `← add_assoc`, `neg_add`, `zero_add` to `{b}`.",
                f"RHS simplifies via `add_zero` to `neg {a}`.",
            ],
            "Watch rewrite direction: `add (neg a) zero = neg a` uses `PureRing.add_zero`.",
            f"by\n"
            f"  have h1 := congrArg (PureRing.add (PureRing.neg {a})) h\n"
            f"  rw [← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.add_zero] at h1\n"
            f"  exact h1",
        )
        emit(
            4,
            RING_PREAMBLE,
            f"theorem ring_mul_neg_{i} {{R : Type}} [PureRing R] ({a} {b} : R) : "
            f"PureRing.mul {a} (PureRing.neg {b}) = PureRing.neg (PureRing.mul {a} {b}) :=",
            [
                f"To prove `mul {a} (neg {b}) = neg (mul {a} {b})`, show `add (mul {a} {b}) (mul {a} (neg {b})) = zero`.",
                f"First establish helper `hz : mul {a} zero = zero` using `left_distrib` and cancellation.",
                f"Then factor `add (mul {a} {b}) (mul {a} (neg {b})) = mul {a} (add {b} (neg {b})) = mul {a} zero = zero`.",
                f"Add `neg (mul {a} {b})` on the left to isolate `mul {a} (neg {b})`.",
            ],
            "Requires a two-lemma chain inside `by`: first `a * 0 = 0`, then `a * b + a * (-b) = 0`, then left-cancellation!",
            f"by\n"
            f"  have hz : PureRing.mul {a} PureRing.zero = PureRing.zero := by\n"
            f"    have h0 : PureRing.add (PureRing.mul {a} PureRing.zero) (PureRing.mul {a} PureRing.zero) = "
            f"PureRing.add (PureRing.mul {a} PureRing.zero) PureRing.zero := by\n"
            f"      rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]\n"
            f"    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul {a} PureRing.zero))) h0\n"
            f"    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'\n"
            f"    exact h0'\n"
            f"  have hsum : PureRing.add (PureRing.mul {a} {b}) (PureRing.mul {a} (PureRing.neg {b})) = PureRing.zero := by\n"
            f"    rw [← PureRing.left_distrib, PureRing.add_neg, hz]\n"
            f"  have hfin := congrArg (PureRing.add (PureRing.neg (PureRing.mul {a} {b}))) hsum\n"
            f"  rw [← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.add_zero] at hfin\n"
            f"  exact hfin",
        )
        emit(
            3,
            RING_PREAMBLE,
            f"theorem ring_neg_neg_{i} {{R : Type}} [PureRing R] ({a} : R) : "
            f"PureRing.neg (PureRing.neg {a}) = {a} :=",
            [
                f"Notice `add (neg {a}) {a} = zero` and also `add (neg {a}) (neg (neg {a})) = zero`.",
                f"Add `neg (neg {a})` or left-cancel `neg {a}`? Wait: left-canceling `neg {a}` requires adding `neg (neg {a})` on the left!",
                f"Equivalently, compute `neg (neg {a}) = add (neg (neg {a})) (add (neg {a}) {a}) = add (add (neg (neg {a})) (neg {a})) {a} = {a}` via `calc`!",
            ],
            "Using `calc` with `neg_add` on `neg a` avoids circularity.",
            f"by\n"
            f"  calc PureRing.neg (PureRing.neg {a})\n"
            f"    _ = PureRing.add (PureRing.neg (PureRing.neg {a})) PureRing.zero := by rw [PureRing.add_zero]\n"
            f"    _ = PureRing.add (PureRing.neg (PureRing.neg {a})) (PureRing.add (PureRing.neg {a}) {a}) := by rw [PureRing.neg_add]\n"
            f"    _ = PureRing.add (PureRing.add (PureRing.neg (PureRing.neg {a})) (PureRing.neg {a})) {a} := by rw [← PureRing.add_assoc]\n"
            f"    _ = PureRing.add PureRing.zero {a} := by rw [PureRing.neg_add]\n"
            f"    _ = {a} := by rw [PureRing.zero_add]",
        )
        emit(
            3,
            RING_PREAMBLE,
            f"theorem ring_distrib_four_{i} {{R : Type}} [PureRing R] ({a} {b} {c} d : R) : "
            f"PureRing.mul (PureRing.add {a} {b}) (PureRing.add {c} d) = "
            f"PureRing.add (PureRing.add (PureRing.mul {a} {c}) (PureRing.mul {a} d)) "
            f"(PureRing.add (PureRing.mul {b} {c}) (PureRing.mul {b} d)) :=",
            [
                f"First apply `PureRing.right_distrib` to split `add {a} {b}` on the left.",
                f"Then apply `PureRing.left_distrib` on both `mul {a} (add {c} d)` and `mul {b} (add {c} d)`.",
            ],
            "Order matters: `right_distrib` splits `(a + b) * X = a * X + b * X`, then `left_distrib` expands each `X = c + d`.",
            "by\n  rw [PureRing.right_distrib, PureRing.left_distrib, PureRing.left_distrib]",
        )

    # Subgroups, intersections, preimages, and centralizers
    for i in range(16):
        emit(
            2,
            SUBGROUP_PREAMBLE,
            f"theorem subgroup_inter_{i} {{G : Type}} [PureGrp G] (H K : G → Prop) "
            f"(hH : IsSubgroup H) (hK : IsSubgroup K) : IsSubgroup (fun x => H x ∧ K x) :=",
            [
                "To prove `fun x => H x ∧ K x` is a subgroup, construct all three `IsSubgroup` fields with `refine ⟨?_, ?_, ?_⟩`.",
                "`one_mem`: pair `hH.one_mem` and `hK.one_mem`.",
                "`mul_mem`: destruct both conjunctions and apply `hH.mul_mem` and `hK.mul_mem`.",
                "`inv_mem`: destruct `⟨hxH, hxK⟩` and apply `hH.inv_mem` and `hK.inv_mem`.",
            ],
            "Keep implicit parameters `{a b}` clean using `rintro` on each structure field.",
            "by\n"
            "  refine ⟨⟨hH.one_mem, hK.one_mem⟩, ?_, ?_⟩\n"
            "  · rintro a b ⟨haH, haK⟩ ⟨hbH, hbK⟩\n"
            "    exact ⟨hH.mul_mem haH hbH, hK.mul_mem haK hbK⟩\n"
            "  · rintro a ⟨haH, haK⟩\n"
            "    exact ⟨hH.inv_mem haH, hK.inv_mem haK⟩",
        )
        emit(
            3,
            SUBGROUP_PREAMBLE,
            f"theorem subgroup_mul_inv_mem_{i} {{G : Type}} [PureGrp G] (H : G → Prop) "
            f"(hH : IsSubgroup H) {{x y : G}} (hx : H x) (hy : H y) : H (PureGrp.mul x (PureGrp.inv y)) :=",
            [
                "By `hH.inv_mem hy`, we have `H (PureGrp.inv y)`.",
                "Combine `hx` and `hH.inv_mem hy` via `hH.mul_mem`.",
            ],
            "One-step subgroup criterion direction: `x ∈ H` and `y ∈ H` implies `x * y⁻¹ ∈ H`.",
            "by\n  exact hH.mul_mem hx (hH.inv_mem hy)",
        )
        emit(
            4,
            SUBGROUP_PREAMBLE,
            f"theorem subgroup_of_one_and_div_{i} {{G : Type}} [PureGrp G] (S : G → Prop) "
            f"(hone : S PureGrp.one) (hdiv : ∀ {{x y}}, S x → S y → S (PureGrp.mul x (PureGrp.inv y))) : "
            f"IsSubgroup S :=",
            [
                "Classic subgroup test! We have `S 1` and `x, y ∈ S → x * y⁻¹ ∈ S`.",
                "First derive `hinv : ∀ a, S a → S (inv a)` by setting `x = one, y = a` in `hdiv`, since `one * inv a = inv a`.",
                "Next prove `inv (inv b) = b` in `PureGrp` using a short `calc` chain.",
                "Finally derive `mul_mem`: for `a, b ∈ S`, we have `inv b ∈ S` by `hinv`, so `a * inv (inv b) ∈ S` by `hdiv`, which rewrites to `a * b ∈ S`!",
            ],
            "Do not assume `PureGrp.inv_inv` exists in the preamble — prove `inv (inv b) = b` locally with `calc`!",
            "by\n"
            "  have hinv : ∀ {a : G}, S a → S (PureGrp.inv a) := by\n"
            "    intro a ha\n"
            "    have h1 := hdiv hone ha\n"
            "    rw [PureGrp.one_mul] at h1\n"
            "    exact h1\n"
            "  have hinv2 : ∀ b : G, PureGrp.inv (PureGrp.inv b) = b := by\n"
            "    intro b\n"
            "    calc PureGrp.inv (PureGrp.inv b)\n"
            "      _ = PureGrp.mul (PureGrp.inv (PureGrp.inv b)) PureGrp.one := by rw [PureGrp.mul_one]\n"
            "      _ = PureGrp.mul (PureGrp.inv (PureGrp.inv b)) (PureGrp.mul (PureGrp.inv b) b) := by rw [PureGrp.inv_mul]\n"
            "      _ = PureGrp.mul (PureGrp.mul (PureGrp.inv (PureGrp.inv b)) (PureGrp.inv b)) b := by rw [← PureGrp.mul_assoc]\n"
            "      _ = b := by rw [PureGrp.inv_mul, PureGrp.one_mul]\n"
            "  refine ⟨hone, ?_, hinv⟩\n"
            "  intro a b ha hb\n"
            "  have h2 := hdiv ha (hinv hb)\n"
            "  rw [hinv2 b] at h2\n"
            "  exact h2",
        )
        emit(
            4,
            SUBGROUP_PREAMBLE,
            f"theorem centralizer_is_subgroup_{i} {{G : Type}} [PureGrp G] (z : G) : "
            f"IsSubgroup (fun x => PureGrp.mul x z = PureGrp.mul z x) :=",
            [
                "We show the centralizer `C(z) = {x | x * z = z * x}` is a subgroup of `G`.",
                "1. `one_mem`: `one * z = z = z * one` via `one_mul` and `mul_one`.",
                "2. `mul_mem`: if `a * z = z * a` and `b * z = z * b`, compute `(a * b) * z = a * (b * z) = a * (z * b) = (a * z) * b = (z * a) * b = z * (a * b)`.",
                "3. `inv_mem`: from `a * z = z * a`, multiply on the left and right by `inv a`: `inv a * z = inv a * (z * a) * inv a = inv a * (a * z) * inv a = z * inv a`.",
            ],
            "Carefully track associativity in `inv_mem` using a `calc` proof.",
            "by\n"
            "  refine ⟨?_, ?_, ?_⟩\n"
            "  · dsimp\n"
            "    rw [PureGrp.one_mul, PureGrp.mul_one]\n"
            "  · intro a b ha hb\n"
            "    dsimp at ha hb ⊢\n"
            "    calc PureGrp.mul (PureGrp.mul a b) z\n"
            "      _ = PureGrp.mul a (PureGrp.mul b z) := by rw [PureGrp.mul_assoc]\n"
            "      _ = PureGrp.mul a (PureGrp.mul z b) := by rw [hb]\n"
            "      _ = PureGrp.mul (PureGrp.mul a z) b := by rw [← PureGrp.mul_assoc]\n"
            "      _ = PureGrp.mul (PureGrp.mul z a) b := by rw [ha]\n"
            "      _ = PureGrp.mul z (PureGrp.mul a b) := by rw [PureGrp.mul_assoc]\n"
            "  · intro a ha\n"
            "    dsimp at ha ⊢\n"
            "    calc PureGrp.mul (PureGrp.inv a) z\n"
            "      _ = PureGrp.mul (PureGrp.mul (PureGrp.inv a) z) PureGrp.one := by rw [PureGrp.mul_one]\n"
            "      _ = PureGrp.mul (PureGrp.mul (PureGrp.inv a) z) (PureGrp.mul a (PureGrp.inv a)) := by rw [PureGrp.mul_inv]\n"
            "      _ = PureGrp.mul (PureGrp.inv a) (PureGrp.mul z (PureGrp.mul a (PureGrp.inv a))) := by rw [PureGrp.mul_assoc]\n"
            "      _ = PureGrp.mul (PureGrp.inv a) (PureGrp.mul (PureGrp.mul z a) (PureGrp.inv a)) := by rw [← PureGrp.mul_assoc z a]\n"
            "      _ = PureGrp.mul (PureGrp.inv a) (PureGrp.mul (PureGrp.mul a z) (PureGrp.inv a)) := by rw [← ha]\n"
            "      _ = PureGrp.mul (PureGrp.mul (PureGrp.inv a) (PureGrp.mul a z)) (PureGrp.inv a) := by rw [← PureGrp.mul_assoc]\n"
            "      _ = PureGrp.mul (PureGrp.mul (PureGrp.mul (PureGrp.inv a) a) z) (PureGrp.inv a) := by rw [← PureGrp.mul_assoc (PureGrp.inv a) a z]\n"
            "      _ = PureGrp.mul z (PureGrp.inv a) := by rw [PureGrp.inv_mul, PureGrp.one_mul]",
        )

    return out


# ---------------------------------------------------------------------------
# Family S2-2: Bounded Lattices, Heyting Algebras & Fixed-Point Order Theory
# ---------------------------------------------------------------------------

HEYTING_PREAMBLE = """\
class BoundedLattice (L : Type) where
  le : L → L → Prop
  bot : L
  top : L
  sup : L → L → L
  inf : L → L → L
  le_refl : ∀ a : L, le a a
  le_trans : ∀ {a b c : L}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b
  bot_le : ∀ a : L, le bot a
  le_top : ∀ a : L, le a top
  le_sup_left : ∀ a b : L, le a (sup a b)
  le_sup_right : ∀ a b : L, le b (sup a b)
  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c
  inf_le_left : ∀ a b : L, le (inf a b) a
  inf_le_right : ∀ a b : L, le (inf a b) b
  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)

class HeytingAlg (H : Type) extends BoundedLattice H where
  himp : H → H → H
  le_himp_iff : ∀ a b c : H, BoundedLattice.le a (himp b c) ↔ BoundedLattice.le (BoundedLattice.inf a b) c"""


def gen_s2_order_heyting(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "order_lattice", steps, pitfall)
        out.append(build_sft_item(idx, "order_lattice", st, diff, pre, hdr, sk, body))
        idx += 1

    vars_h = [
        ("a", "b", "c"),
        ("x", "y", "z"),
        ("p", "q", "r"),
        ("u", "v", "w"),
        ("e1", "e2", "e3"),
        ("s1", "s2", "s3"),
        ("m1", "m2", "m3"),
        ("k1", "k2", "k3"),
        ("d1", "d2", "d3"),
        ("t1", "t2", "t3"),
        ("g1", "g2", "g3"),
        ("n1", "n2", "n3"),
    ]
    for i, (a, b, c) in enumerate(vars_h):
        emit(
            2,
            HEYTING_PREAMBLE,
            f"theorem bdd_sup_bot_{i} {{L : Type}} [BoundedLattice L] ({a} : L) : "
            f"BoundedLattice.sup {a} BoundedLattice.bot = {a} :=",
            [
                "Apply `BoundedLattice.le_antisymm`.",
                "`sup a bot ≤ a` holds via `sup_le` using `le_refl a` and `bot_le a`.",
                "`a ≤ sup a bot` holds immediately by `le_sup_left`.",
            ],
            "Always prove lattice equalities via `le_antisymm`.",
            f"by\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · exact BoundedLattice.sup_le (BoundedLattice.le_refl {a}) (BoundedLattice.bot_le {a})\n"
            f"  · exact BoundedLattice.le_sup_left {a} BoundedLattice.bot",
        )
        emit(
            2,
            HEYTING_PREAMBLE,
            f"theorem bdd_inf_top_{i} {{L : Type}} [BoundedLattice L] ({a} : L) : "
            f"BoundedLattice.inf {a} BoundedLattice.top = {a} :=",
            [
                "Apply `le_antisymm`: `inf a top ≤ a` by `inf_le_left`, and `a ≤ inf a top` by `le_inf (le_refl a) (le_top a)`.",
            ],
            "Check argument order of `le_inf`: `le a b → le a c → le a (inf b c)`.",
            f"by\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · exact BoundedLattice.inf_le_left {a} BoundedLattice.top\n"
            f"  · exact BoundedLattice.le_inf (BoundedLattice.le_refl {a}) (BoundedLattice.le_top {a})",
        )
        emit(
            2,
            HEYTING_PREAMBLE,
            f"theorem bdd_inf_bot_{i} {{L : Type}} [BoundedLattice L] ({a} : L) : "
            f"BoundedLattice.inf {a} BoundedLattice.bot = BoundedLattice.bot :=",
            [
                "`inf a bot ≤ bot` by `inf_le_right`, and `bot ≤ inf a bot` by `bot_le`.",
            ],
            "`bot` is absorbing for `inf`.",
            f"by\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · exact BoundedLattice.inf_le_right {a} BoundedLattice.bot\n"
            f"  · exact BoundedLattice.bot_le _",
        )
        emit(
            2,
            HEYTING_PREAMBLE,
            f"theorem bdd_sup_top_{i} {{L : Type}} [BoundedLattice L] ({a} : L) : "
            f"BoundedLattice.sup {a} BoundedLattice.top = BoundedLattice.top :=",
            [
                "`sup a top ≤ top` by `le_top`, and `top ≤ sup a top` by `le_sup_right`.",
            ],
            "`top` is absorbing for `sup`.",
            f"by\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · exact BoundedLattice.le_top _\n"
            f"  · exact BoundedLattice.le_sup_right {a} BoundedLattice.top",
        )
        emit(
            3,
            HEYTING_PREAMBLE,
            f"theorem heyting_modus_ponens_{i} {{H : Type}} [HeytingAlg H] ({a} {b} : H) : "
            f"BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp {a} {b}) {a}) {b} :=",
            [
                f"Residuation `HeytingAlg.le_himp_iff x {a} {b}` says `le x (himp {a} {b}) ↔ le (inf x {a}) {b}`.",
                f"Instantiate `x = himp {a} {b}` and apply `.mp` to `le_refl (himp {a} {b})`!",
            ],
            "Heyting modus ponens is simply the counit of the `( - ⊓ a ) ⊣ ( a ⇨ - )` adjunction.",
            f"by\n  exact (HeytingAlg.le_himp_iff (HeytingAlg.himp {a} {b}) {a} {b}).mp (BoundedLattice.le_refl _)",
        )
        emit(
            3,
            HEYTING_PREAMBLE,
            f"theorem heyting_self_top_{i} {{H : Type}} [HeytingAlg H] ({a} : H) : "
            f"HeytingAlg.himp {a} {a} = BoundedLattice.top :=",
            [
                f"Use `le_antisymm`: `himp {a} {a} ≤ top` is immediate from `le_top`.",
                f"For `top ≤ himp {a} {a}`, rewrite via `le_himp_iff` to `inf top {a} ≤ {a}`, which is `inf_le_right`!",
            ],
            "Use `(HeytingAlg.le_himp_iff _ _ _).mpr` whenever `himp` is on the RHS of `≤`.",
            f"by\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · exact BoundedLattice.le_top _\n"
            f"  · exact (HeytingAlg.le_himp_iff BoundedLattice.top {a} {a}).mpr (BoundedLattice.inf_le_right _ _)",
        )
        emit(
            3,
            HEYTING_PREAMBLE,
            f"theorem heyting_mono_right_{i} {{H : Type}} [HeytingAlg H] ({a} {b} {c} : H) "
            f"(hbc : BoundedLattice.le {b} {c}) : BoundedLattice.le (HeytingAlg.himp {a} {b}) (HeytingAlg.himp {a} {c}) :=",
            [
                f"Apply `(HeytingAlg.le_himp_iff _ {a} {c}).mpr`.",
                f"We need `inf (himp {a} {b}) {a} ≤ {c}`.",
                f"Chain modus ponens `inf (himp {a} {b}) {a} ≤ {b}` with `hbc : {b} ≤ {c}` via `le_trans`.",
            ],
            "`himp a _` is covariant (monotone) in its second argument.",
            f"by\n"
            f"  apply (HeytingAlg.le_himp_iff _ {a} {c}).mpr\n"
            f"  have hmp : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp {a} {b}) {a}) {b} := "
            f"(HeytingAlg.le_himp_iff _ {a} {b}).mp (BoundedLattice.le_refl _)\n"
            f"  exact BoundedLattice.le_trans hmp hbc",
        )
        emit(
            4,
            HEYTING_PREAMBLE,
            f"theorem heyting_anti_left_{i} {{H : Type}} [HeytingAlg H] ({a} {b} {c} : H) "
            f"(hab : BoundedLattice.le {a} {b}) : BoundedLattice.le (HeytingAlg.himp {b} {c}) (HeytingAlg.himp {a} {c}) :=",
            [
                f"`himp _ {c}` is contravariant (antitone) in its first argument!",
                f"Transpose via `le_himp_iff`: we must show `inf (himp {b} {c}) {a} ≤ {c}`.",
                f"First show `inf (himp {b} {c}) {a} ≤ inf (himp {b} {c}) {b}` using `le_inf`, `inf_le_left`, and `inf_le_right` + `hab`.",
                f"Then chain with modus ponens `inf (himp {b} {c}) {b} ≤ {c}`.",
            ],
            "Notice the order reversal `{a} ≤ {b} → ({b} ⇨ {c}) ≤ ({a} ⇨ {c})`.",
            f"by\n"
            f"  apply (HeytingAlg.le_himp_iff _ {a} {c}).mpr\n"
            f"  have h1 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp {b} {c}) {a}) "
            f"(BoundedLattice.inf (HeytingAlg.himp {b} {c}) {b}) := by\n"
            f"    apply BoundedLattice.le_inf (BoundedLattice.inf_le_left _ _)\n"
            f"    exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) hab\n"
            f"  have hmp : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp {b} {c}) {b}) {c} := "
            f"(HeytingAlg.le_himp_iff _ {b} {c}).mp (BoundedLattice.le_refl _)\n"
            f"  exact BoundedLattice.le_trans h1 hmp",
        )
        emit(
            4,
            HEYTING_PREAMBLE,
            f"theorem heyting_himp_inf_right_{i} {{H : Type}} [HeytingAlg H] ({a} {b} {c} : H) : "
            f"HeytingAlg.himp {a} (BoundedLattice.inf {b} {c}) = "
            f"BoundedLattice.inf (HeytingAlg.himp {a} {b}) (HeytingAlg.himp {a} {c}) :=",
            [
                f"Prove `a ⇨ (b ⊓ c) = (a ⇨ b) ⊓ (a ⇨ c)` by `le_antisymm`.",
                f"LHS ≤ RHS: use `le_inf`, and in each branch apply `le_himp_iff` + modus ponens + `inf_le_left` / `inf_le_right`.",
                f"RHS ≤ LHS: apply `le_himp_iff` then `le_inf`; project `(a ⇨ b) ⊓ (a ⇨ c)` to `a ⇨ b` (resp. `a ⇨ c`) and apply modus ponens!",
            ],
            "Right adjoints preserve meets! Break into clear `have` steps for readability and reliability.",
            f"by\n"
            f"  have hmp_bc : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp {a} (BoundedLattice.inf {b} {c})) {a}) (BoundedLattice.inf {b} {c}) := "
            f"(HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)\n"
            f"  apply BoundedLattice.le_antisymm\n"
            f"  · apply BoundedLattice.le_inf\n"
            f"    · exact (HeytingAlg.le_himp_iff _ _ _).mpr (BoundedLattice.le_trans hmp_bc (BoundedLattice.inf_le_left _ _))\n"
            f"    · exact (HeytingAlg.le_himp_iff _ _ _).mpr (BoundedLattice.le_trans hmp_bc (BoundedLattice.inf_le_right _ _))\n"
            f"  · apply (HeytingAlg.le_himp_iff _ _ _).mpr\n"
            f"    apply BoundedLattice.le_inf\n"
            f"    · have hl : BoundedLattice.le (BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp {a} {b}) (HeytingAlg.himp {a} {c})) {a}) "
            f"(BoundedLattice.inf (HeytingAlg.himp {a} {b}) {a}) := by\n"
            f"        apply BoundedLattice.le_inf\n"
            f"        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_left _ _)\n"
            f"        · exact BoundedLattice.inf_le_right _ _\n"
            f"      exact BoundedLattice.le_trans hl ((HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _))\n"
            f"    · have hr : BoundedLattice.le (BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp {a} {b}) (HeytingAlg.himp {a} {c})) {a}) "
            f"(BoundedLattice.inf (HeytingAlg.himp {a} {c}) {a}) := by\n"
            f"        apply BoundedLattice.le_inf\n"
            f"        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_right _ _)\n"
            f"        · exact BoundedLattice.inf_le_right _ _\n"
            f"      exact BoundedLattice.le_trans hr ((HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _))",
        )

    return out


# ---------------------------------------------------------------------------
# Family S2-3: Transitive Closure `PlusR`, `StarR`, Simulations & Determinism
# ---------------------------------------------------------------------------

PLUS_STAR_PREAMBLE = """\
inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : StarStep R x x
  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z

inductive PlusStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | single {x y : α} : R x y → PlusStep R x y
  | step {x y z : α} : R x y → PlusStep R y z → PlusStep R x z

def Simulates {α β : Type} (R : α → α → Prop) (T : β → β → Prop) (sim : α → β → Prop) : Prop :=
  ∀ {a1 a2 b1}, sim a1 b1 → R a1 a2 → ∃ b2, T b1 b2 ∧ sim a2 b2"""


def gen_s2_relations_sim(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "relations_sets", steps, pitfall)
        out.append(build_sft_item(idx, "relations_sets", st, diff, pre, hdr, sk, body))
        idx += 1

    for i in range(20):
        emit(
            2,
            PLUS_STAR_PREAMBLE,
            f"theorem plus_to_star_{i} {{α : Type}} (R : α → α → Prop) {{x y : α}} "
            f"(hp : PlusStep R x y) : StarStep R x y :=",
            [
                "Induct on `hp : PlusStep R x y`.",
                "Case `single hxy`: wrap into `StarStep.step hxy (StarStep.refl _)`.",
                "Case `step hxy _ ih`: apply `StarStep.step hxy ih`.",
            ],
            "`PlusStep` is the non-empty path relation, so every `PlusStep` embeds into `StarStep`.",
            "by\n"
            "  induction hp with\n"
            "  | single hxy => exact StarStep.step hxy (StarStep.refl _)\n"
            "  | step hxy _ ih => exact StarStep.step hxy ih",
        )
        emit(
            3,
            PLUS_STAR_PREAMBLE,
            f"theorem step_star_to_plus_{i} {{α : Type}} (R : α → α → Prop) {{x y z : α}} "
            f"(h1 : R x y) (h2 : StarStep R y z) : PlusStep R x z :=",
            [
                "Wait: if we induct on `h2 : StarStep R y z`, `x` and `h1 : R x y` depend on `y`, so we MUST generalize `x` (`revert x` or `induction h2 generalizing x`)!",
                "Let's check `induction h2 generalizing x`:",
                "- `refl`: `h1 : R x y`, goal `PlusStep R x y`, proved by `PlusStep.single h1`.",
                "- `step hyw _ ih`: `h1 : R x y`, `ih hyw : PlusStep R y z`, so `PlusStep.step h1 (ih hyw)` proves `PlusStep R x z`!",
            ],
            "CRITICAL Lean 4 tactic insight: use `induction h2 generalizing x` because `y` changes in the `step` case!",
            "by\n"
            "  induction h2 generalizing x with\n"
            "  | refl _ => exact PlusStep.single h1\n"
            "  | step hyw _ ih => exact PlusStep.step h1 (ih hyw)",
        )
        emit(
            4,
            PLUS_STAR_PREAMBLE,
            f"theorem plus_iff_step_star_{i} {{α : Type}} (R : α → α → Prop) (x z : α) : "
            f"PlusStep R x z ↔ ∃ y, R x y ∧ StarStep R y z :=",
            [
                "Split `↔` with `constructor`.",
                "Forward (`PlusStep R x z → ∃ y, R x y ∧ StarStep R y z`): induct on `PlusStep`.",
                "  - `single hxz`: witness `z`, giving `⟨z, hxz, StarStep.refl z⟩`.",
                "  - `step hxy _ ih`: unpack `⟨w, hyw, hstar⟩ := ih` and return `⟨y, hxy, StarStep.step hyw hstar⟩`.",
                "Backward: destruct `⟨y, hxy, hstar⟩` and induct on `hstar generalizing x`!",
            ],
            "Remember `generalizing x` in the backward direction when inducting on `StarStep R y z`.",
            "by\n"
            "  constructor\n"
            "  · intro hp\n"
            "    induction hp with\n"
            "    | single hxz => exact ⟨_, hxz, StarStep.refl _⟩\n"
            "    | step hxy _ ih =>\n"
            "      rcases ih with ⟨w, hyw, hstar⟩\n"
            "      exact ⟨_, hxy, StarStep.step hyw hstar⟩\n"
            "  · rintro ⟨y, hxy, hstar⟩\n"
            "    induction hstar generalizing x with\n"
            "    | refl _ => exact PlusStep.single hxy\n"
            "    | step hyw _ ih => exact PlusStep.step hxy (ih hyw)",
        )
        emit(
            3,
            PLUS_STAR_PREAMBLE,
            f"theorem plus_trans_{i} {{α : Type}} (R : α → α → Prop) {{x y z : α}} "
            f"(h1 : PlusStep R x y) (h2 : PlusStep R y z) : PlusStep R x z :=",
            [
                "Induct on `h1 : PlusStep R x y` keeping `z` fixed.",
                "In `single hxy`, `PlusStep.step hxy h2` closes the goal directly.",
                "In `step hxy _ ih`, `PlusStep.step hxy (ih h2)` closes the goal.",
            ],
            "Inducting on the first derivation `h1` avoids needing a snoc helper.",
            "by\n"
            "  induction h1 with\n"
            "  | single hxy => exact PlusStep.step hxy h2\n"
            "  | step hxy _ ih => exact PlusStep.step hxy (ih h2)",
        )
        emit(
            4,
            PLUS_STAR_PREAMBLE,
            f"theorem simulation_star_lift_{i} {{α β : Type}} (R : α → α → Prop) (T : β → β → Prop) "
            f"(sim : α → β → Prop) (hsim : Simulates R T sim) {{a1 a2 : α}} {{b1 : β}} "
            f"(hab : sim a1 b1) (hsteps : StarStep R a1 a2) : ∃ b2, StarStep T b1 b2 ∧ sim a2 b2 :=",
            [
                "Classic operational semantics lemma: single-step simulation lifts to `StarStep`!",
                "Crucial detail: as `a1` steps to an intermediate `a_mid`, `b1` also changes to `b_mid`! So we MUST run `induction hsteps generalizing b1`.",
                "Base `refl a`: choose `b2 = b1`, giving `⟨b1, StarStep.refl b1, hab⟩`.",
                "Step `step hra1m _ ih`: apply `hsim hab hra1m` to get `⟨b_mid, htb1m, hsim_m⟩`, then apply `ih hsim_m` to get `⟨b2, htstar, hsim2⟩`, and prepend `StarStep.step htb1m htstar`!",
            ],
            "Without `generalizing b1`, the induction hypothesis would fix `b1` and fail in the inductive step!",
            "by\n"
            "  induction hsteps generalizing b1 with\n"
            "  | refl a => exact ⟨b1, StarStep.refl b1, hab⟩\n"
            "  | step hr _ ih =>\n"
            "    rcases hsim hab hr with ⟨b_mid, ht1, hsim_mid⟩\n"
            "    rcases ih hsim_mid with ⟨b2, ht_rest, hsim2⟩\n"
            "    exact ⟨b2, StarStep.step ht1 ht_rest, hsim2⟩",
        )
        emit(
            3,
            PLUS_STAR_PREAMBLE,
            f"theorem deterministic_confluence_step_{i} {{α : Type}} (R : α → α → Prop) "
            f"(hdet : ∀ {{x y1 y2}}, R x y1 → R x y2 → y1 = y2) {{a b1 b2 : α}} "
            f"(h1 : StarStep R a b1) (h2 : StarStep R a b2) "
            f"(hnf1 : ∀ z, ¬ R b1 z) (hnf2 : ∀ z, ¬ R b2 z) : b1 = b2 :=",
            [
                "Unique normal forms for deterministic transition systems!",
                "Induct on `h1` (`StarStep R a b1`):",
                "- `refl`: `a` is already `b1`, which is in normal form (`hnf1`). Inspect `h2` by `cases h2`: `refl` gives `rfl`; `step hr _` contradicts `hnf1 _ hr`!",
                "- `step hr1 _ ih`: inspect `h2` by `cases h2`: `refl` contradicts `hnf2 _ hr1`; `step hr2 h2_tail` gives equal next states by `hdet hr1 hr2`, substitute and apply `ih`!",
            ],
            "Combining `induction h1` with `cases h2` cleanly handles both `refl` and `step` interactions.",
            "by\n"
            "  induction h1 with\n"
            "  | refl a =>\n"
            "    cases h2 with\n"
            "    | refl => rfl\n"
            "    | step hr2 _ => exact False.elim (hnf1 _ hr2)\n"
            "  | step hr1 _ ih =>\n"
            "    cases h2 with\n"
            "    | refl => exact False.elim (hnf2 _ hr1)\n"
            "    | step hr2 h2_rest =>\n"
            "      have heq := hdet hr1 hr2\n"
            "      subst heq\n"
            "      exact ih h2_rest hnf1",
        )

    return out


# ---------------------------------------------------------------------------
# Family S2-4: Cantor Diagonalization, Option/Sum/Prod Monads & Higher-Order Logic
# ---------------------------------------------------------------------------

MONAD_LOGIC_PREAMBLE = """\
def SurjectiveFn {α β : Type} (f : α → β) : Prop := ∀ b : β, ∃ a : α, f a = b
def InjectiveFn {α β : Type} (f : α → β) : Prop := ∀ ⦃a1 a2 : α⦄, f a1 = f a2 → a1 = a2

def optMap {α β : Type} (f : α → β) : Option α → Option β
  | none => none
  | some x => some (f x)

def optBind {α β : Type} : Option α → (α → Option β) → Option β
  | none, _ => none
  | some x, f => f x"""


def gen_s2_logic_monads(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "logic_functions", steps, pitfall)
        out.append(build_sft_item(idx, "logic_functions", st, diff, pre, hdr, sk, body))
        idx += 1

    for i in range(20):
        emit(
            4,
            MONAD_LOGIC_PREAMBLE,
            f"theorem cantor_no_surj_{i} (α : Type) (f : α → (α → Prop)) : ¬ SurjectiveFn f :=",
            [
                "Cantor's diagonal argument in pure Lean 4!",
                "Assume `hsurj : SurjectiveFn f` and define the diagonal predicate `D : α → Prop := fun x => ¬ f x x`.",
                "By surjectivity at `D`, obtain `a : α` such that `ha : f a = D`.",
                "Evaluate `ha` at `a` using `congrFun ha a` (or `have hiff : f a a ↔ ¬ f a a` after `rw`!): `f a a = (¬ f a a)`.",
                "Derive contradiction: first prove `hn : ¬ f a a` by `intro h; have h' : ¬ f a a := Eq.mp ... h; exact h' h`, then feed `hn` back into the reverse equality!",
            ],
            "In Lean 4, `congrFun ha a` turns `f a = (fun x => ¬ f x x)` into `f a a = (¬ f a a)`.",
            "by\n"
            "  intro hsurj\n"
            "  rcases hsurj (fun x => ¬ f x x) with ⟨a, ha⟩\n"
            "  have hdiag : f a a = (¬ f a a) := congrFun ha a\n"
            "  have hna : ¬ f a a := by\n"
            "    intro hfaa\n"
            "    have hn : ¬ f a a := Eq.mp hdiag hfaa\n"
            "    exact hn hfaa\n"
            "  exact hna (Eq.mpr hdiag hna)",
        )
        emit(
            4,
            MONAD_LOGIC_PREAMBLE,
            f"theorem lawvere_prop_fixpoint_{i} (α : Type) (f : α → (α → Prop)) "
            f"(hsurj : SurjectiveFn f) (g : Prop → Prop) : ∃ P : Prop, g P ↔ P :=",
            [
                "Lawvere's fixed-point theorem specialized to `Prop`!",
                "Define `D : α → Prop := fun x => g (f x x)` and obtain `a : α` with `ha : f a = D` from `hsurj`.",
                "By `congrFun ha a`, we get `f a a = g (f a a)`.",
                "Choose witness `P = f a a`; rewriting with that equality gives `g (f a a) ↔ f a a`!",
            ],
            "Notice how Cantor's theorem is the special case `g = Not` of this fixed-point theorem.",
            "by\n"
            "  rcases hsurj (fun x => g (f x x)) with ⟨a, ha⟩\n"
            "  have heq : f a a = g (f a a) := congrFun ha a\n"
            "  refine ⟨f a a, ?_⟩\n"
            "  rw [← heq]",
        )
        emit(
            2,
            MONAD_LOGIC_PREAMBLE,
            f"theorem optBind_right_id_{i} {{α : Type}} (mx : Option α) : optBind mx some = mx :=",
            [
                "Case-split on `mx : Option α` (`none` vs `some x`).",
                "Both branches reduce definitionally via `rfl`.",
            ],
            "Right identity monad law on `Option`.",
            "by\n  cases mx <;> rfl",
        )
        emit(
            3,
            MONAD_LOGIC_PREAMBLE,
            f"theorem optBind_assoc_{i} {{α β γ : Type}} (mx : Option α) (f : α → Option β) (g : β → Option γ) : "
            f"optBind (optBind mx f) g = optBind mx (fun x => optBind (f x) g) :=",
            [
                "Monad associativity for `Option`.",
                "Case-split on `mx`: for `none`, both sides evaluate to `none`; for `some x`, both evaluate to `optBind (f x) g`.",
            ],
            "Do not case-split on `f x` unnecessarily — splitting on `mx` suffices!",
            "by\n  cases mx <;> rfl",
        )
        emit(
            3,
            MONAD_LOGIC_PREAMBLE,
            f"theorem optMap_eq_bind_{i} {{α β : Type}} (f : α → β) (mx : Option α) : "
            f"optMap f mx = optBind mx (fun x => some (f x)) :=",
            [
                "Relate functorial `optMap` to monadic `optBind` by `cases mx <;> rfl`.",
            ],
            "Simple case analysis on `Option α`.",
            "by\n  cases mx <;> rfl",
        )
        emit(
            3,
            MONAD_LOGIC_PREAMBLE,
            f"theorem drinker_paradox_classical_{i} {{α : Type}} (x0 : α) (D : α → Prop) : "
            f"∃ x : α, D x → ∀ y : α, D y :=",
            [
                "Smullyan's Drinker Paradox in classical first-order logic (given non-empty witness `x0 : α`)!",
                "Split on `Classical.em (∀ y : α, D y)`:",
                "- `inl hall`: pick witness `x0`; then `fun _ => hall` proves `D x0 → ∀ y, D y`.",
                "- `inr hnall`: we prove `∃ x, ¬ D x` by `Classical.byContradiction`, or directly get `x` with `¬ D x`; then `D x → ∀ y, D y` holds vacuously!",
            ],
            "Cannot be proved constructively; requires `Classical.em` on the quantified formula `∀ y, D y`!",
            "by\n"
            "  cases Classical.em (∀ y : α, D y) with\n"
            "  | inl hall => exact ⟨x0, fun _ => hall⟩\n"
            "  | inr hnall =>\n"
            "    have hex : ∃ x : α, ¬ D x := by\n"
            "      apply Classical.byContradiction\n"
            "      intro hno\n"
            "      apply hnall\n"
            "      intro y\n"
            "      cases Classical.em (D y) with\n"
            "      | inl hdy => exact hdy\n"
            "      | inr hndy => exact False.elim (hno ⟨y, hndy⟩)\n"
            "    rcases hex with ⟨x, hnx⟩\n"
            "    exact ⟨x, fun hdx => False.elim (hnx hdx)⟩",
        )
        emit(
            3,
            MONAD_LOGIC_PREAMBLE,
            f"theorem barber_irreflexive_{i} {{α : Type}} (shaves : α → α → Prop) : "
            f"¬ ∃ b : α, ∀ x : α, shaves b x ↔ ¬ shaves x x :=",
            [
                "Russell's Barber Paradox (purely constructive, zero classical axioms needed)!",
                "Destruct `⟨b, hb⟩` and instantiate `hb` at `x = b` to get `shaves b b ↔ ¬ shaves b b`.",
                "First prove `hnb : ¬ shaves b b` via `intro h; exact (hb b).mp h h`, then apply `hnb ((hb b).mpr hnb)`.",
            ],
            "No `Classical.em` required for `¬(P ↔ ¬P)`.",
            "by\n"
            "  rintro ⟨b, hb⟩\n"
            "  have hbb := hb b\n"
            "  have hnb : ¬ shaves b b := fun h => hbb.mp h h\n"
            "  exact hnb (hbb.mpr hnb)",
        )
        emit(
            3,
            MONAD_LOGIC_PREAMBLE,
            f"theorem prod_swap_bij_{i} (α β : Type) : "
            f"InjectiveFn (fun p : α × β => (p.2, p.1)) ∧ SurjectiveFn (fun p : α × β => (p.2, p.1)) :=",
            [
                "Prove `Prod.swap` is both injective and surjective.",
                "Injective: destruct pairs `⟨a1, b1⟩` and `⟨a2, b2⟩`, inject tuple equality via `Prod.mk.inj`.",
                "Surjective: for `(b, a)`, provide witness `(a, b)`.",
            ],
            "Destructuring `α × β` with `rintro ⟨a, b⟩` makes projections definitional.",
            "by\n"
            "  constructor\n"
            "  · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h\n"
            "    cases h\n"
            "    rfl\n"
            "  · rintro ⟨b, a⟩\n"
            "    exact ⟨(a, b), rfl⟩",
        )

    return out


# ---------------------------------------------------------------------------
# Family S2-5: Accumulator Generalization, Folds/Filters & Stack-Machine Compiler
# ---------------------------------------------------------------------------

ACC_COMPILER_PREAMBLE = """\
def sumL2 : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL2 xs

def sumAcc : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => sumAcc xs (acc + x)

def revAcc {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def filterL {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: filterL p xs else filterL p xs

def foldrL {α β : Type} (f : α → β → β) (z : β) : List α → β
  | [] => z
  | x :: xs => f x (foldrL f z xs)"""

STACK_VM_PREAMBLE = """\
inductive AddExpr where
  | lit : Nat → AddExpr
  | add : AddExpr → AddExpr → AddExpr

def evalAdd : AddExpr → Nat
  | AddExpr.lit n => n
  | AddExpr.add e1 e2 => evalAdd e1 + evalAdd e2

inductive VMInstr where
  | push : Nat → VMInstr
  | addTop : VMInstr

def runVM : List VMInstr → List Nat → List Nat
  | [], stk => stk
  | VMInstr.push n :: code, stk => runVM code (n :: stk)
  | VMInstr.addTop :: code, b :: a :: stk => runVM code ((a + b) :: stk)
  | VMInstr.addTop :: code, stk => runVM code stk

def compileAdd : AddExpr → List VMInstr
  | AddExpr.lit n => [VMInstr.push n]
  | AddExpr.add e1 e2 => compileAdd e1 ++ compileAdd e2 ++ [VMInstr.addTop]"""


def gen_s2_accumulators_vm(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "inductive_ds", steps, pitfall)
        out.append(build_sft_item(idx, "inductive_ds", st, diff, pre, hdr, sk, body))
        idx += 1

    for i in range(22):
        emit(
            3,
            ACC_COMPILER_PREAMBLE,
            f"theorem sumAcc_eq_add_sum_{i} (xs : List Nat) (acc : Nat) : "
            f"sumAcc xs acc = acc + sumL2 xs :=",
            [
                "Tail-recursive accumulator lemma! Because `sumAcc (x :: xs) acc` calls `sumAcc xs (acc + x)`, `acc` changes at each recursive step.",
                "Therefore we MUST run `induction xs generalizing acc`!",
                "Base `nil`: `acc = acc + 0` (`omega`).",
                "Step `cons x tl ih`: unfold `sumAcc` and `sumL2`, rewrite with `ih (acc + x)`, and finish `(acc + x) + sumL2 tl = acc + (x + sumL2 tl)` via `Nat.add_assoc`!",
            ],
            "Forgetting `generalizing acc` makes the inductive hypothesis unusable on `acc + x`!",
            "by\n"
            "  induction xs generalizing acc with\n"
            "  | nil => simp [sumAcc, sumL2]\n"
            "  | cons x tl ih =>\n"
            "    simp [sumAcc, sumL2, ih (acc + x), Nat.add_assoc]",
        )
        emit(
            4,
            ACC_COMPILER_PREAMBLE,
            f"theorem sumAcc_zero_correct_{i} (xs : List Nat) : sumAcc xs 0 = sumL2 xs :=",
            [
                "Direct induction on `xs` at `acc = 0` FAILS because the recursive call has `acc = 0 + x`!",
                "Formulate helper `have haux : ∀ (ys : List Nat) (acc : Nat), sumAcc ys acc = acc + sumL2 ys` proved by `induction ys generalizing acc`.",
                "Instantiate `haux xs 0` and simplify `0 + sumL2 xs`.",
            ],
            "Classic accumulator generalization trap: always lift `0` to an arbitrary `acc : Nat` in a `have` lemma.",
            "by\n"
            "  have haux : ∀ (ys : List Nat) (acc : Nat), sumAcc ys acc = acc + sumL2 ys := by\n"
            "    intro ys\n"
            "    induction ys with\n"
            "    | nil => intro acc; simp [sumAcc, sumL2]\n"
            "    | cons y tl ih => intro acc; simp [sumAcc, sumL2, ih (acc + y), Nat.add_assoc]\n"
            "  simpa using haux xs 0",
        )
        emit(
            3,
            ACC_COMPILER_PREAMBLE,
            f"theorem revAcc_append_acc_{i} {{α : Type}} (xs acc : List α) : "
            f"revAcc xs acc = revAcc xs [] ++ acc :=",
            [
                "Induct on `xs generalizing acc`.",
                "Wait: in `cons x tl`, `revAcc (x :: tl) acc = revAcc tl (x :: acc)` and `revAcc (x :: tl) [] ++ acc = revAcc tl [x] ++ acc`.",
                "Use `ih (x :: acc)` on the LHS (`revAcc tl [] ++ (x :: acc)`) and `ih [x]` on the RHS (`(revAcc tl [] ++ [x]) ++ acc`), then equate via `List.append_assoc`!",
            ],
            "Applying `ih` twice — once at `x :: acc` and once at `[x]` — avoids needing `List.reverse`!",
            "by\n"
            "  induction xs generalizing acc with\n"
            "  | nil => simp [revAcc]\n"
            "  | cons x tl ih =>\n"
            "    simp only [revAcc]\n"
            "    rw [ih (x :: acc), ih [x], List.append_assoc]\n"
            "    rfl",
        )
        emit(
            3,
            ACC_COMPILER_PREAMBLE,
            f"theorem filterL_append_{i} {{α : Type}} (p : α → Bool) (xs ys : List α) : "
            f"filterL p (xs ++ ys) = filterL p xs ++ filterL p ys :=",
            [
                "Induct on `xs`.",
                "`nil`: both sides reduce to `filterL p ys`.",
                "`cons x tl ih`: unfold `filterL`, split on `hpx : p x` with `cases p x`, and rewrite by `ih`.",
            ],
            "Case-splitting on the boolean `p x` resolves the `if ... then ... else ...` cleanly.",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih =>\n"
            "    simp only [List.cons_append, filterL]\n"
            "    cases p x <;> simp [ih]",
        )
        emit(
            4,
            ACC_COMPILER_PREAMBLE,
            f"theorem filterL_idem_{i} {{α : Type}} (p : α → Bool) (xs : List α) : "
            f"filterL p (filterL p xs) = filterL p xs :=",
            [
                "Induct on `xs`.",
                "In `cons x tl ih`, split on `hp : p x`:",
                "- When `p x = false`, `filterL p (x :: tl)` is `filterL p tl`, so `ih` finishes immediately.",
                "- When `p x = true`, `filterL p (x :: tl)` is `x :: filterL p tl`. Applying `filterL p` again tests `p x` a second time, which we STILL know is `true` via `hp`! Then rewrite by `ih`!",
            ],
            "Must retain the equation `hp : p x = true` (`cases hp : p x`) so the outer `if p x` also simplifies!",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih =>\n"
            "    simp only [filterL]\n"
            "    cases hp : p x with\n"
            "    | false => exact ih\n"
            "    | true => simp [filterL, hp, ih]",
        )
        emit(
            3,
            ACC_COMPILER_PREAMBLE,
            f"theorem filterL_length_le_{i} {{α : Type}} (p : α → Bool) (xs : List α) : "
            f"(filterL p xs).length ≤ xs.length :=",
            [
                "Induct on `xs`.",
                "`nil`: `0 ≤ 0`.",
                "`cons x tl ih`: split on `p x`; either `(filterL p tl).length ≤ tl.length + 1` or `(filterL p tl).length + 1 ≤ tl.length + 1`, both solved by `omega` from `ih`!",
            ],
            "Combine `cases p x` with `simp` and `omega`.",
            "by\n"
            "  induction xs with\n"
            "  | nil => decide\n"
            "  | cons x tl ih =>\n"
            "    simp only [filterL]\n"
            "    cases p x <;> simp <;> omega",
        )
        emit(
            3,
            ACC_COMPILER_PREAMBLE,
            f"theorem foldrL_append_{i} {{α β : Type}} (f : α → β → β) (z : β) (xs ys : List α) : "
            f"foldrL f z (xs ++ ys) = foldrL f (foldrL f z ys) xs :=",
            [
                "Universal foldr-append fusion law! Induct on `xs`.",
                "`nil`: `foldrL f z ys = foldrL f z ys`.",
                "`cons x tl ih`: `f x (foldrL f z (tl ++ ys)) = f x (foldrL f (foldrL f z ys) tl)` by `ih`.",
            ],
            "Notice how `foldrL f z ys` becomes the new base accumulator for folding over `xs`.",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [foldrL, ih]",
        )
        emit(
            4,
            STACK_VM_PREAMBLE,
            f"theorem vm_run_append_{i} (c1 c2 : List VMInstr) (stk : List Nat) : "
            f"runVM (c1 ++ c2) stk = runVM c2 (runVM c1 stk) :=",
            [
                "Prove instruction execution is compositional over `++`: `runVM (c1 ++ c2) stk = runVM c2 (runVM c1 stk)`.",
                "Induct on `c1 generalizing stk`!",
                "In `cons instr rest ih`, case-split on `instr`: for `push n`, apply `ih (n :: stk)`; for `addTop`, match `stk` on `[]`, `[x]`, `b :: a :: s` so `runVM` reduces cleanly in every case!",
            ],
            "Matching `stk` into `[]`, `[x]`, and `b :: a :: s` ensures `runVM`'s 4-clause pattern match reduces.",
            "by\n"
            "  induction c1 generalizing stk with\n"
            "  | nil => rfl\n"
            "  | cons instr rest ih =>\n"
            "    cases instr with\n"
            "    | push n => exact ih (n :: stk)\n"
            "    | addTop =>\n"
            "      rcases stk with _ | ⟨b, _ | ⟨a, s⟩⟩\n"
            "      · exact ih []\n"
            "      · exact ih [b]\n"
            "      · exact ih ((a + b) :: s)",
        )
        emit(
            4,
            STACK_VM_PREAMBLE,
            f"theorem compileAdd_correct_{i} (e : AddExpr) (stk : List Nat) : "
            f"runVM (compileAdd e) stk = evalAdd e :: stk :=",
            [
                "Classic McCarthy-Painter stack compiler correctness theorem!",
                "First establish helper `hrun : ∀ (c1 c2 : List VMInstr) (s : List Nat), runVM (c1 ++ c2) s = runVM c2 (runVM c1 s)`.",
                "Now induct on `e : AddExpr generalizing stk`:",
                "- `lit n`: `runVM [push n] stk = n :: stk = evalAdd (lit n) :: stk`.",
                "- `add e1 e2 ih1 ih2`: rewrite `compileAdd (add e1 e2)` with `hrun` twice: first `e1` pushes `v1 :: stk`, then `e2` pushes `v2 :: v1 :: stk`, then `[addTop]` pops `v2, v1` and pushes `(v1 + v2) :: stk`!",
            ],
            "Notice why `runVM` pops `b` first then `a` to push `a + b`: `e2` was evaluated AFTER `e1` so `evalAdd e2` sits on top of the stack!",
            "by\n"
            "  have hrun : ∀ (c1 c2 : List VMInstr) (s : List Nat), runVM (c1 ++ c2) s = runVM c2 (runVM c1 s) := by\n"
            "    intro c1 c2\n"
            "    induction c1 with\n"
            "    | nil => intro s; rfl\n"
            "    | cons instr rest ih =>\n"
            "      intro s\n"
            "      cases instr with\n"
            "      | push n => exact ih (n :: s)\n"
            "      | addTop =>\n"
            "        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩\n"
            "        · exact ih []\n"
            "        · exact ih [b]\n"
            "        · exact ih ((a + b) :: s')\n"
            "  induction e generalizing stk with\n"
            "  | lit n => rfl\n"
            "  | add e1 e2 ih1 ih2 =>\n"
            "    simp only [compileAdd, evalAdd]\n"
            "    rw [List.append_assoc, hrun, ih1, hrun, ih2]\n"
            "    rfl",
        )

    return out


# ---------------------------------------------------------------------------
# Family S2-6: Int/Nat Modular Congruence, Powers, Series & Divisibility
# ---------------------------------------------------------------------------

INT_MOD_PREAMBLE = """\
def ModEqInt (m a b : Int) : Prop := ∃ k : Int, a - b = m * k

def powNat (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powNat b n * b"""


def gen_s2_number_theory(start_idx: int) -> List[SketchpadSFTItem]:
    out: List[SketchpadSFTItem] = []
    idx = start_idx

    def emit(diff: int, pre: str, hdr: str, steps: List[str], pitfall: str, body: str):
        nonlocal idx
        st, sk = render_sketchpad_style(idx, hdr, "nat_number_theory", steps, pitfall)
        out.append(build_sft_item(idx, "nat_number_theory", st, diff, pre, hdr, sk, body))
        idx += 1

    for i in range(22):
        emit(
            2,
            INT_MOD_PREAMBLE,
            f"theorem modEq_refl_{i} (m a : Int) : ModEqInt m a a :=",
            [
                "Unfold `ModEqInt`: we need `k : Int` such that `a - a = m * k`.",
                "Pick `k = 0`; `omega` or `Int.mul_zero` discharges `a - a = m * 0`.",
            ],
            "Pick witness `0` for reflexivity of modular congruence.",
            "by\n  exact ⟨0, by omega⟩",
        )
        emit(
            2,
            INT_MOD_PREAMBLE,
            f"theorem modEq_symm_{i} (m a b : Int) (h : ModEqInt m a b) : ModEqInt m b a :=",
            [
                "Destruct `h` into `⟨k, hk⟩` with `a - b = m * k`.",
                "Provide witness `-k`: `b - a = -(a - b) = -(m * k) = m * (-k)` via `Int.mul_neg` and `omega`.",
            ],
            "Notice `m * (-k)` is nonlinear if `m` and `k` are both variables, so rewrite `Int.mul_neg` before `omega`!",
            "by\n"
            "  rcases h with ⟨k, hk⟩\n"
            "  refine ⟨-k, ?_⟩\n"
            "  rw [Int.mul_neg]\n"
            "  omega",
        )
        emit(
            3,
            INT_MOD_PREAMBLE,
            f"theorem modEq_trans_{i} (m a b c : Int) (h1 : ModEqInt m a b) (h2 : ModEqInt m b c) : "
            f"ModEqInt m a c :=",
            [
                "Unpack `⟨k1, hk1⟩` and `⟨k2, hk2⟩`.",
                "Choose witness `k1 + k2`; expand `m * (k1 + k2) = m * k1 + m * k2` via `Int.mul_add`, then `(a - b) + (b - c) = a - c` via `omega`!",
            ],
            "`omega` handles linear integer arithmetic once `Int.mul_add` expands `m * (k1 + k2)`.",
            "by\n"
            "  rcases h1 with ⟨k1, hk1⟩\n"
            "  rcases h2 with ⟨k2, hk2⟩\n"
            "  refine ⟨k1 + k2, ?_⟩\n"
            "  rw [Int.mul_add]\n"
            "  omega",
        )
        emit(
            3,
            INT_MOD_PREAMBLE,
            f"theorem modEq_add_compat_{i} (m a1 b1 a2 b2 : Int) "
            f"(h1 : ModEqInt m a1 b1) (h2 : ModEqInt m a2 b2) : ModEqInt m (a1 + a2) (b1 + b2) :=",
            [
                "Unpack `⟨k1, hk1⟩` and `⟨k2, hk2⟩`.",
                "Choose witness `k1 + k2`, expand `Int.mul_add`, and finish `(a1 + a2) - (b1 + b2) = (a1 - b1) + (a2 - b2)` with `omega`.",
            ],
            "Expand `m * (k1 + k2)` first with `Int.mul_add`.",
            "by\n"
            "  rcases h1 with ⟨k1, hk1⟩\n"
            "  rcases h2 with ⟨k2, hk2⟩\n"
            "  refine ⟨k1 + k2, ?_⟩\n"
            "  rw [Int.mul_add]\n"
            "  omega",
        )
        emit(
            3,
            INT_MOD_PREAMBLE,
            f"theorem modEq_sub_compat_{i} (m a1 b1 a2 b2 : Int) "
            f"(h1 : ModEqInt m a1 b1) (h2 : ModEqInt m a2 b2) : ModEqInt m (a1 - a2) (b1 - b2) :=",
            [
                "Choose witness `k1 - k2`, expand `Int.mul_sub`, and finish with `omega`.",
            ],
            "Use `Int.mul_sub` to turn `m * (k1 - k2)` into `m * k1 - m * k2`.",
            "by\n"
            "  rcases h1 with ⟨k1, hk1⟩\n"
            "  rcases h2 with ⟨k2, hk2⟩\n"
            "  refine ⟨k1 - k2, ?_⟩\n"
            "  rw [Int.mul_sub]\n"
            "  omega",
        )
        emit(
            3,
            INT_MOD_PREAMBLE,
            f"theorem powNat_add_{i} (b m n : Nat) : powNat b (m + n) = powNat b m * powNat b n :=",
            [
                "Check `powNat` recursion: `powNat b (n + 1) = powNat b n * b`.",
                "Induct on `n` so `m + (k + 1) = (m + k) + 1` via `Nat.add_succ`.",
                "Unfold `powNat`, apply `ih`, and reassociate via `Nat.mul_assoc`.",
            ],
            "Inducting on `n` matches right-associated `+` in Lean 4!",
            "by\n"
            "  induction n with\n"
            "  | zero => simp [powNat]\n"
            "  | succ k ih =>\n"
            "    rw [Nat.add_succ, powNat, powNat, ih, Nat.mul_assoc]",
        )
        emit(
            4,
            INT_MOD_PREAMBLE,
            f"theorem powNat_mul_exp_{i} (b m n : Nat) : powNat b (m * n) = powNat (powNat b m) n :=",
            [
                "To prove `b^(m * n) = (b^m)^n`, first establish helper `hadd : ∀ x y, powNat b (x + y) = powNat b x * powNat b y`.",
                "Then induct on `n`:",
                "- `zero`: `m * 0 = 0`, so `1 = 1`.",
                "- `succ k ih`: `m * (k + 1) = m * k + m` (`Nat.mul_succ`); apply `hadd`, rewrite with `ih`, and match `powNat (powNat b m) (k + 1)`!",
            ],
            "Needs the exponent-addition lemma `hadd` inside `by` before inducting on `n`.",
            "by\n"
            "  have hadd : ∀ x y : Nat, powNat b (x + y) = powNat b x * powNat b y := by\n"
            "    intro x y\n"
            "    induction y with\n"
            "    | zero => simp [powNat]\n"
            "    | succ k ih => rw [Nat.add_succ, powNat, powNat, ih, Nat.mul_assoc]\n"
            "  induction n with\n"
            "  | zero => simp [powNat]\n"
            "  | succ k ih =>\n"
            "    rw [Nat.mul_succ, hadd, ih, powNat]",
        )
        emit(
            4,
            INT_MOD_PREAMBLE,
            f"theorem powNat_mul_base_{i} (a b n : Nat) : powNat (a * b) n = powNat a n * powNat b n :=",
            [
                "Prove `(a * b)^n = a^n * b^n` by induction on `n`.",
                "In `succ k ih`, `(a^k * b^k) * (a * b)` must rearrange to `(a^k * a) * (b^k * b)`.",
                "Rearrange cleanly using `Nat.mul_assoc` and `Nat.mul_comm (powNat b k) a`!",
            ],
            "Do not call `omega` on nonlinear multiplication `(a^k * b^k) * (a * b)`; rewrite explicitly with `Nat.mul_assoc` and `Nat.mul_comm`.",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    simp only [powNat, ih]\n"
            "    rw [Nat.mul_assoc (powNat a k) (powNat b k) (a * b)]\n"
            "    rw [← Nat.mul_assoc (powNat b k) a b]\n"
            "    rw [Nat.mul_comm (powNat b k) a]\n"
            "    rw [Nat.mul_assoc a (powNat b k) b]\n"
            "    rw [← Nat.mul_assoc (powNat a k) a (powNat b k * b)]",
        )

    return out


def augment_from_stage1(
    stage1_path: str,
    start_idx: int,
    target_total: int = 2150,
    seed: int = 123,
) -> List[SketchpadSFTItem]:
    """
    Convert medium/hard Stage 1 verified theorems into diverse `<sketchpad>` SFT examples
    so the SFT model also masters `<sketchpad>` reasoning across all Stage 1 pure Lean structures.
    """
    if not os.path.exists(stage1_path):
        return []
    raw_items: List[Dict] = []
    with open(stage1_path, "r", encoding="utf-8") as f:
        for line in f:
            if line.strip():
                raw_items.append(json.loads(line))

    # Prioritize difficulty >= 2 first, then difficulty 1
    rng = random.Random(seed)
    rng.shuffle(raw_items)
    raw_items.sort(key=lambda x: -int(x.get("difficulty", 1)))

    out: List[SketchpadSFTItem] = []
    idx = start_idx
    for row in raw_items:
        if idx >= target_total:
            break
        notes = row.get("sketch_notes") or ["Inspect hypotheses and apply pure Lean 4 tactics."]
        # Add tactic inspection cue based on proof body
        pbody = row["proof_body"]
        extra = []
        if "induction " in pbody:
            extra.append("Check base case and inductive step carefully so the induction hypothesis applies cleanly.")
        if "calc " in pbody:
            extra.append("Structure the multi-step equality as an explicit `calc` chain.")
        if "Classical." in pbody:
            extra.append("Constructive elimination does not suffice here; invoke `Classical.em` / `Classical.byContradiction`.")
        if "have " in pbody:
            extra.append("Introduce an intermediate `have` sublemma before closing the main goal.")

        st, sk = render_sketchpad_style(
            idx,
            row["theorem_header"],
            row["domain"],
            notes + extra,
        )
        out.append(
            build_sft_item(
                idx=idx,
                domain=row["domain"],
                style=st,
                difficulty=int(row.get("difficulty", 2)),
                preamble=row["preamble"],
                theorem_header=row["theorem_header"],
                sketchpad=sk,
                proof_body=pbody,
            )
        )
        idx += 1
    return out


def generate_stage2_sft(
    stage1_path: str = "data/stage1_pure_lean.jsonl",
    out_path: str = "data/stage2_sketchpad_sft.jsonl",
    seed: int = 2026,
) -> Dict:
    t0 = time.time()
    new_items: List[SketchpadSFTItem] = []
    for fn in [
        gen_s2_algebra,
        gen_s2_order_heyting,
        gen_s2_relations_sim,
        gen_s2_logic_monads,
        gen_s2_accumulators_vm,
        gen_s2_number_theory,
    ]:
        new_items.extend(fn(len(new_items)))

    print(f"Synthesized {len(new_items)} brand-new Stage 2 sketchpad theorems. Verifying with Lean 4.36...")
    valid_idx, failed = verify_snippets_batch([it.full_lean for it in new_items], chunk_size=75, max_workers=8)
    if failed:
        print(f"WARNING: {len(failed)} new Stage 2 items failed Lean check:")
        for fi, err in failed[:5]:
            print(f"  - [{new_items[fi].id}]: {err[:220]}")

    verified_new = [new_items[i] for i in valid_idx]
    augmented = augment_from_stage1(stage1_path, start_idx=len(verified_new), target_total=2150, seed=seed)
    all_sft = verified_new + augmented

    rng = random.Random(seed)
    rng.shuffle(all_sft)

    # Split into train (2050) and val (remainder ~100)
    val_size = min(100, max(50, len(all_sft) - 2050))
    val_items = all_sft[:val_size]
    train_items = all_sft[val_size:]

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    val_path = out_path.replace(".jsonl", "_val.jsonl")

    style_counts: Dict[str, int] = {}
    domain_counts: Dict[str, int] = {}

    with open(out_path, "w", encoding="utf-8") as f:
        for it in train_items:
            style_counts[it.style] = style_counts.get(it.style, 0) + 1
            domain_counts[it.domain] = domain_counts.get(it.domain, 0) + 1
            f.write(json.dumps(it.to_dict(), ensure_ascii=False) + "\n")

    with open(val_path, "w", encoding="utf-8") as f:
        for it in val_items:
            f.write(json.dumps(it.to_dict(), ensure_ascii=False) + "\n")

    summary = {
        "new_candidates": len(new_items),
        "new_verified": len(verified_new),
        "new_failed": len(failed),
        "augmented_from_stage1": len(augmented),
        "train_sft_count": len(train_items),
        "val_sft_count": len(val_items),
        "domains": domain_counts,
        "styles": style_counts,
        "elapsed_sec": round(time.time() - t0, 2),
        "train_path": out_path,
        "val_path": val_path,
    }
    print("Stage 2 SFT Summary:", json.dumps(summary, indent=2))
    return summary


if __name__ == "__main__":
    generate_stage2_sft()
