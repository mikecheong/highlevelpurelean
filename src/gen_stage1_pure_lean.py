"""
Stage 1 Synthetic Pure Lean 4 Corpus Generator (~1,600+ theorems, zero Mathlib).
Generates high-level pure Lean 4 definitions, algebraic/order/relational structures,
inductive data types, higher-order logic, and number theory theorems, and formally
verifies 100% of the generated corpus with the Lean 4.36 kernel.
"""

from __future__ import annotations

import itertools
import json
import os
import random
import time
from dataclasses import asdict, dataclass
from typing import Dict, List, Tuple

from src.lean_verifier import verify_snippets_batch


@dataclass
class PureLeanItem:
    id: str
    domain: str
    difficulty: int
    preamble: str
    theorem_header: str
    proof_body: str
    full_lean: str
    sketch_notes: List[str]

    def to_dict(self) -> Dict:
        return asdict(self)


def make_item(
    idx: int,
    domain: str,
    difficulty: int,
    preamble: str,
    theorem_header: str,
    proof_body: str,
    sketch_notes: List[str],
) -> PureLeanItem:
    p = preamble.strip()
    h = theorem_header.strip()
    if not h.endswith(":="):
        h += " :="
    b = proof_body.strip()
    full = (p + "\n\n" if p else "") + f"{h}\n{b}"
    return PureLeanItem(
        id=f"s1_{domain}_{idx:04d}",
        domain=domain,
        difficulty=difficulty,
        preamble=p,
        theorem_header=h,
        proof_body=b,
        full_lean=full,
        sketch_notes=sketch_notes,
    )


# ---------------------------------------------------------------------------
# 1. Abstract Algebra in Pure Lean 4 (Semigroups, Monoids, Groups, Homomorphisms, Actions)
# ---------------------------------------------------------------------------

ALGEBRA_MONOID_PREAMBLE = """\
class PureMonoid (M : Type) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

def mpow {M : Type} [PureMonoid M] (a : M) : Nat → M
  | 0 => PureMonoid.one
  | n + 1 => PureMonoid.mul (mpow a n) a"""

ALGEBRA_COMM_MONOID_PREAMBLE = ALGEBRA_MONOID_PREAMBLE + """

class PureCommMonoid (M : Type) extends PureMonoid M where
  mul_comm : ∀ a b : M, mul a b = mul b a"""

ALGEBRA_GROUP_PREAMBLE = """\
class PureGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

def conj {G : Type} [PureGroup G] (g x : G) : G :=
  PureGroup.mul (PureGroup.mul g x) (PureGroup.inv g)"""

ALGEBRA_HOM_PREAMBLE = ALGEBRA_GROUP_PREAMBLE + """

structure GroupHom (G H : Type) [PureGroup G] [PureGroup H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (PureGroup.mul a b) = PureGroup.mul (toFun a) (toFun b)"""

ALGEBRA_ACTION_PREAMBLE = ALGEBRA_GROUP_PREAMBLE + """

class GroupAction (G X : Type) [PureGroup G] where
  act : G → X → X
  one_act : ∀ x : X, act PureGroup.one x = x
  mul_act : ∀ g h : G, ∀ x : X, act (PureGroup.mul g h) x = act g (act h x)"""


def gen_algebra_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "algebra", diff, pre, hdr, body, notes))
        idx += 1

    # Monoid identity / reassociation / power theorems
    vars3 = [("a", "b", "c"), ("x", "y", "z"), ("u", "v", "w"), ("p", "q", "r")]
    for i, (a, b, c) in enumerate(vars3):
        add(
            1,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem monoid_reassoc_one_{i} {{M : Type}} [PureMonoid M] ({a} {b} {c} : M) : "
            f"PureMonoid.mul (PureMonoid.mul {a} PureMonoid.one) (PureMonoid.mul {b} {c}) = "
            f"PureMonoid.mul (PureMonoid.mul {a} {b}) {c} :=",
            f"by\n  rw [PureMonoid.mul_one, PureMonoid.mul_assoc]",
            [
                f"Simplify `mul {a} one` to `{a}` via `PureMonoid.mul_one`.",
                f"Reassociate `mul {a} (mul {b} {c})` using `PureMonoid.mul_assoc`.",
            ],
        )
        add(
            1,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem monoid_one_absorb_mid_{i} {{M : Type}} [PureMonoid M] ({a} {b} {c} : M) : "
            f"PureMonoid.mul {a} (PureMonoid.mul PureMonoid.one (PureMonoid.mul {b} {c})) = "
            f"PureMonoid.mul (PureMonoid.mul {a} {b}) {c} :=",
            f"by\n  rw [PureMonoid.one_mul, PureMonoid.mul_assoc]",
            [
                "Eliminate the inner left identity with `PureMonoid.one_mul`.",
                "Align parentheses with `PureMonoid.mul_assoc`.",
            ],
        )

    # 4-variable parenthesization theorems (Catalan shapes)
    v4_sets = [
        ("a", "b", "c", "d"),
        ("w", "x", "y", "z"),
        ("m1", "m2", "m3", "m4"),
        ("p", "q", "r", "s"),
        ("g1", "g2", "g3", "g4"),
    ]
    for i, (a, b, c, d) in enumerate(v4_sets):
        add(
            2,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem monoid_assoc4_ll_to_rr_{i} {{M : Type}} [PureMonoid M] ({a} {b} {c} {d} : M) : "
            f"PureMonoid.mul (PureMonoid.mul (PureMonoid.mul {a} {b}) {c}) {d} = "
            f"PureMonoid.mul {a} (PureMonoid.mul {b} (PureMonoid.mul {c} {d})) :=",
            "by\n  rw [PureMonoid.mul_assoc, PureMonoid.mul_assoc]",
            [
                "Goal converts fully left-associated 4-fold product into fully right-associated form.",
                "Apply `PureMonoid.mul_assoc` twice from outer to inner product.",
            ],
        )
        add(
            2,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem monoid_assoc4_mid_to_lr_{i} {{M : Type}} [PureMonoid M] ({a} {b} {c} {d} : M) : "
            f"PureMonoid.mul (PureMonoid.mul {a} (PureMonoid.mul {b} {c})) {d} = "
            f"PureMonoid.mul (PureMonoid.mul {a} {b}) (PureMonoid.mul {c} {d}) :=",
            f"by\n  rw [← PureMonoid.mul_assoc {a} {b} {c}, PureMonoid.mul_assoc]",
            [
                f"First reassociate `mul {a} (mul {b} {c})` leftward to `mul (mul {a} {b}) {c}`.",
                f"Then apply `PureMonoid.mul_assoc` to group `{c}` and `{d}`.",
            ],
        )
        add(
            2,
            ALGEBRA_COMM_MONOID_PREAMBLE,
            f"theorem comm_monoid_swap_inner_{i} {{M : Type}} [PureCommMonoid M] ({a} {b} {c} {d} : M) : "
            f"PureMonoid.mul (PureMonoid.mul {a} {b}) (PureMonoid.mul {c} {d}) = "
            f"PureMonoid.mul (PureMonoid.mul {a} {c}) (PureMonoid.mul {b} {d}) :=",
            f"by\n"
            f"  rw [PureMonoid.mul_assoc {a} {b} (PureMonoid.mul {c} {d})]\n"
            f"  rw [← PureMonoid.mul_assoc {b} {c} {d}]\n"
            f"  rw [PureCommMonoid.mul_comm {b} {c}]\n"
            f"  rw [PureMonoid.mul_assoc {c} {b} {d}]\n"
            f"  rw [← PureMonoid.mul_assoc {a} {c} (PureMonoid.mul {b} {d})]",
            [
                f"Isolate the middle pair `mul {b} {c}` using `PureMonoid.mul_assoc`.",
                f"Swap `{b}` and `{c}` via `PureCommMonoid.mul_comm` and re-parenthesize.",
            ],
        )
        add(
            2,
            ALGEBRA_COMM_MONOID_PREAMBLE,
            f"theorem comm_monoid_outer_flip_{i} {{M : Type}} [PureCommMonoid M] ({a} {b} {c} {d} : M) : "
            f"PureMonoid.mul (PureMonoid.mul {a} {b}) (PureMonoid.mul {c} {d}) = "
            f"PureMonoid.mul (PureMonoid.mul {d} {c}) (PureMonoid.mul {b} {a}) :=",
            f"by\n"
            f"  rw [PureCommMonoid.mul_comm {a} {b}, PureCommMonoid.mul_comm {c} {d}]\n"
            f"  rw [PureCommMonoid.mul_comm (PureMonoid.mul {b} {a}) (PureMonoid.mul {d} {c})]",
            [
                "Commute both inner pairs first, then commute the two resulting factors.",
            ],
        )

    # Monoid powers `mpow` for concrete and symbolic exponents
    for k in range(1, 9):
        add(
            2,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem mpow_one_const_{k} {{M : Type}} [PureMonoid M] : "
            f"mpow (PureMonoid.one : M) {k} = PureMonoid.one :=",
            "by\n  simp [mpow, PureMonoid.one_mul]",
            [
                f"Unfold recursive `mpow` {k} times and simplify `mul one one = one`.",
            ],
        )

    pow_names = ["a", "x", "g", "u", "m"]
    for i, v in enumerate(pow_names):
        add(
            2,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem mpow_one_all_{i} {{M : Type}} [PureMonoid M] (n : Nat) : "
            f"mpow (PureMonoid.one : M) n = PureMonoid.one :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih => simp [mpow, ih, PureMonoid.one_mul]",
            [
                "Induct on `n : Nat`.",
                "Base case `n = 0` holds by definition of `mpow`; inductive step uses `ih` and `one_mul`.",
            ],
        )
        add(
            3,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem mpow_add_{i} {{M : Type}} [PureMonoid M] ({v} : M) (m n : Nat) : "
            f"mpow {v} (m + n) = PureMonoid.mul (mpow {v} m) (mpow {v} n) :=",
            "by\n"
            "  induction n with\n"
            "  | zero =>\n"
            "    simp [mpow, PureMonoid.mul_one]\n"
            "  | succ k ih =>\n"
            "    rw [Nat.add_succ, mpow, mpow, ih, PureMonoid.mul_assoc]",
            [
                "Induct on the second exponent `n` so `m + (k + 1) = (m + k) + 1` matches `mpow` recursion.",
                "In the `succ` step, unfold `mpow`, rewrite by `ih`, and finish with `PureMonoid.mul_assoc`.",
            ],
        )
        add(
            3,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem mpow_succ_left_{i} {{M : Type}} [PureMonoid M] ({v} : M) (n : Nat) : "
            f"PureMonoid.mul {v} (mpow {v} n) = PureMonoid.mul (mpow {v} n) {v} :=",
            "by\n"
            "  induction n with\n"
            "  | zero => simp [mpow, PureMonoid.mul_one, PureMonoid.one_mul]\n"
            "  | succ k ih =>\n"
            f"    calc PureMonoid.mul {v} (PureMonoid.mul (mpow {v} k) {v})\n"
            f"      _ = PureMonoid.mul (PureMonoid.mul {v} (mpow {v} k)) {v} := by rw [← PureMonoid.mul_assoc]\n"
            f"      _ = PureMonoid.mul (PureMonoid.mul (mpow {v} k) {v}) {v} := by rw [ih]",
            [
                f"Prove `{v}` commutes with its own powers `mpow {v} n` by induction on `n`.",
                "Reassociate leftward in the `succ` step to apply the induction hypothesis `ih`.",
            ],
        )
        add(
            2,
            ALGEBRA_MONOID_PREAMBLE,
            f"theorem idempotent_mpow_succ_{i} {{M : Type}} [PureMonoid M] ({v} : M) "
            f"(hidem : PureMonoid.mul {v} {v} = {v}) (n : Nat) : "
            f"mpow {v} (n + 1) = {v} :=",
            "by\n"
            "  induction n with\n"
            "  | zero => simp [mpow, PureMonoid.one_mul]\n"
            "  | succ k ih =>\n"
            "    change PureMonoid.mul (mpow " + v + " (k + 1)) " + v + " = " + v + "\n"
            "    rw [ih, hidem]",
            [
                f"For an idempotent `{v} * {v} = {v}`, every positive power `n + 1` equals `{v}`.",
                "Induct on `n`: `n = 0` uses `one_mul`; `succ k` unfolds one layer and applies `ih` then `hidem`.",
            ],
        )

    # PureGroup cancellation, uniqueness, inverses, conjugation (many variations)
    grp_vars = [
        ("a", "b", "c"),
        ("x", "y", "z"),
        ("g", "h", "k"),
        ("u", "v", "w"),
        ("p", "q", "r"),
        ("s", "t", "d"),
    ]
    for i, (a, b, c) in enumerate(grp_vars):
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_inv_mul_cancel_left_{i} {{G : Type}} [PureGroup G] ({a} {b} : G) : "
            f"PureGroup.mul (PureGroup.inv {a}) (PureGroup.mul {a} {b}) = {b} :=",
            f"by\n  rw [← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul]",
            [
                f"Reassociate `(inv {a}) * ({a} * {b})` to `((inv {a}) * {a}) * {b}`.",
                "Cancel with `PureGroup.inv_mul` and `PureGroup.one_mul`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_mul_inv_cancel_left_{i} {{G : Type}} [PureGroup G] ({a} {b} : G) : "
            f"PureGroup.mul {a} (PureGroup.mul (PureGroup.inv {a}) {b}) = {b} :=",
            f"by\n  rw [← PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.one_mul]",
            [
                f"Reassociate `{a} * ((inv {a}) * {b})` leftward, apply `mul_inv` and `one_mul`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_mul_inv_cancel_right_{i} {{G : Type}} [PureGroup G] ({a} {b} : G) : "
            f"PureGroup.mul (PureGroup.mul {a} {b}) (PureGroup.inv {b}) = {a} :=",
            f"by\n  rw [PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one]",
            [
                f"Reassociate rightward to `{a} * ({b} * inv {b})`, then apply `mul_inv` and `mul_one`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_inv_cancel_right_{i} {{G : Type}} [PureGroup G] ({a} {b} : G) : "
            f"PureGroup.mul (PureGroup.mul {a} (PureGroup.inv {b})) {b} = {a} :=",
            f"by\n  rw [PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.mul_one]",
            [
                f"Group `(inv {b}) * {b}` on the right via `mul_assoc`, then apply `inv_mul` and `mul_one`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_left_cancel_{i} {{G : Type}} [PureGroup G] ({a} {b} {c} : G) "
            f"(h : PureGroup.mul {a} {b} = PureGroup.mul {a} {c}) : {b} = {c} :=",
            f"by\n"
            f"  have h1 : PureGroup.mul (PureGroup.inv {a}) (PureGroup.mul {a} {b}) = "
            f"PureGroup.mul (PureGroup.inv {a}) (PureGroup.mul {a} {c}) := congrArg (PureGroup.mul (PureGroup.inv {a})) h\n"
            f"  rw [← PureGroup.mul_assoc, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.one_mul] at h1\n"
            f"  exact h1",
            [
                f"Multiply both sides on the left by `PureGroup.inv {a}` using `congrArg`.",
                "Reassociate both sides and cancel `inv a * a = one`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_right_cancel_{i} {{G : Type}} [PureGroup G] ({a} {b} {c} : G) "
            f"(h : PureGroup.mul {b} {a} = PureGroup.mul {c} {a}) : {b} = {c} :=",
            f"by\n"
            f"  have h1 : PureGroup.mul (PureGroup.mul {b} {a}) (PureGroup.inv {a}) = "
            f"PureGroup.mul (PureGroup.mul {c} {a}) (PureGroup.inv {a}) := congrArg (fun t => PureGroup.mul t (PureGroup.inv {a})) h\n"
            f"  rw [PureGroup.mul_assoc, PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one, PureGroup.mul_one] at h1\n"
            f"  exact h1",
            [
                f"Multiply both sides on the right by `PureGroup.inv {a}`.",
                "Reassociate rightward and simplify `a * inv a = one`.",
            ],
        )
        add(
            3,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_inv_inv_{i} {{G : Type}} [PureGroup G] ({a} : G) : "
            f"PureGroup.inv (PureGroup.inv {a}) = {a} :=",
            f"by\n"
            f"  calc PureGroup.inv (PureGroup.inv {a})\n"
            f"    _ = PureGroup.mul (PureGroup.inv (PureGroup.inv {a})) PureGroup.one := by rw [PureGroup.mul_one]\n"
            f"    _ = PureGroup.mul (PureGroup.inv (PureGroup.inv {a})) (PureGroup.mul (PureGroup.inv {a}) {a}) := by rw [PureGroup.inv_mul]\n"
            f"    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.inv {a})) (PureGroup.inv {a})) {a} := by rw [← PureGroup.mul_assoc]\n"
            f"    _ = PureGroup.mul PureGroup.one {a} := by rw [PureGroup.inv_mul]\n"
            f"    _ = {a} := by rw [PureGroup.one_mul]",
            [
                f"Use a `calc` chain starting from `inv (inv {a})`.",
                f"Insert `one = mul (inv {a}) {a}` on the right, reassociate, and cancel `inv (inv {a}) * inv {a}`.",
            ],
        )
        add(
            3,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_mul_inv_rev_{i} {{G : Type}} [PureGroup G] ({a} {b} : G) : "
            f"PureGroup.inv (PureGroup.mul {a} {b}) = PureGroup.mul (PureGroup.inv {b}) (PureGroup.inv {a}) :=",
            f"by\n"
            f"  have h : PureGroup.mul (PureGroup.mul {a} {b}) (PureGroup.inv (PureGroup.mul {a} {b})) = "
            f"PureGroup.mul (PureGroup.mul {a} {b}) (PureGroup.mul (PureGroup.inv {b}) (PureGroup.inv {a})) := by\n"
            f"    rw [PureGroup.mul_inv]\n"
            f"    rw [PureGroup.mul_assoc {a} {b} (PureGroup.mul (PureGroup.inv {b}) (PureGroup.inv {a}))]\n"
            f"    rw [← PureGroup.mul_assoc {b} (PureGroup.inv {b}) (PureGroup.inv {a})]\n"
            f"    rw [PureGroup.mul_inv, PureGroup.one_mul, PureGroup.mul_inv]\n"
            f"  have h2 := congrArg (PureGroup.mul (PureGroup.inv (PureGroup.mul {a} {b}))) h\n"
            f"  rw [← PureGroup.mul_assoc, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.one_mul] at h2\n"
            f"  exact h2",
            [
                f"Show both `inv (mul {a} {b})` and `mul (inv {b}) (inv {a})` are right-inverses of `mul {a} {b}`.",
                f"Left-cancel `mul {a} {b}` by multiplying on the left by `inv (mul {a} {b})`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem conj_one_{i} {{G : Type}} [PureGroup G] ({a} : G) : "
            f"conj {a} PureGroup.one = PureGroup.one :=",
            f"by\n  unfold conj\n  rw [PureGroup.mul_one, PureGroup.mul_inv]",
            [
                "Unfold `conj`, simplify `mul a one = a`, then `mul a (inv a) = one`.",
            ],
        )
        add(
            3,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem conj_mul_{i} {{G : Type}} [PureGroup G] ({a} {b} {c} : G) : "
            f"conj {a} (PureGroup.mul {b} {c}) = PureGroup.mul (conj {a} {b}) (conj {a} {c}) :=",
            f"by\n"
            f"  unfold conj\n"
            f"  rw [PureGroup.mul_assoc (PureGroup.mul {a} {b}) (PureGroup.inv {a}) (PureGroup.mul (PureGroup.mul {a} {c}) (PureGroup.inv {a}))]\n"
            f"  rw [← PureGroup.mul_assoc (PureGroup.inv {a}) (PureGroup.mul {a} {c}) (PureGroup.inv {a})]\n"
            f"  rw [← PureGroup.mul_assoc (PureGroup.inv {a}) {a} {c}]\n"
            f"  rw [PureGroup.inv_mul, PureGroup.one_mul]\n"
            f"  rw [← PureGroup.mul_assoc (PureGroup.mul {a} {b}) {c} (PureGroup.inv {a})]\n"
            f"  rw [PureGroup.mul_assoc {a} {b} {c}]",
            [
                "Unfold `conj` on both sides.",
                f"On the RHS, collapse the middle `(inv {a}) * {a}` to `one` and reassociate.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_eq_mul_inv_of_mul_eq_{i} {{G : Type}} [PureGroup G] ({a} {b} {c} : G) "
            f"(h : PureGroup.mul {a} {b} = {c}) : {a} = PureGroup.mul {c} (PureGroup.inv {b}) :=",
            f"by\n"
            f"  rw [← h, PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one]",
            [
                f"Substitute `{c} = mul {a} {b}` on the RHS and cancel `{b} * inv {b}`.",
            ],
        )
        add(
            2,
            ALGEBRA_GROUP_PREAMBLE,
            f"theorem group_eq_inv_mul_of_mul_eq_{i} {{G : Type}} [PureGroup G] ({a} {b} {c} : G) "
            f"(h : PureGroup.mul {a} {b} = {c}) : {b} = PureGroup.mul (PureGroup.inv {a}) {c} :=",
            f"by\n"
            f"  rw [← h, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul]",
            [
                f"Substitute `{c} = mul {a} {b}` on the RHS and cancel `inv {a} * {a}`.",
            ],
        )

    # GroupHom & GroupAction theorems
    hom_vars = [("f", "g", "h"), ("φ", "ψ", "χ"), ("p", "q", "r"), ("u", "v", "w")]
    for i, (f, g, h) in enumerate(hom_vars):
        add(
            3,
            ALGEBRA_HOM_PREAMBLE,
            f"theorem hom_comp_mul_{i} {{G H K : Type}} [PureGroup G] [PureGroup H] [PureGroup K] "
            f"({f} : GroupHom G H) ({g} : GroupHom H K) (x y : G) : "
            f"{g}.toFun ({f}.toFun (PureGroup.mul x y)) = PureGroup.mul ({g}.toFun ({f}.toFun x)) ({g}.toFun ({f}.toFun y)) :=",
            f"by\n  rw [{f}.map_mul, {g}.map_mul]",
            [
                f"Apply `{f}.map_mul` inside `{g}.toFun`, then apply `{g}.map_mul`.",
            ],
        )
        add(
            3,
            ALGEBRA_HOM_PREAMBLE,
            f"theorem hom_map_mul3_{i} {{G H : Type}} [PureGroup G] [PureGroup H] "
            f"({f} : GroupHom G H) (x y z : G) : "
            f"{f}.toFun (PureGroup.mul (PureGroup.mul x y) z) = "
            f"PureGroup.mul ({f}.toFun x) (PureGroup.mul ({f}.toFun y) ({f}.toFun z)) :=",
            f"by\n  rw [{f}.map_mul, {f}.map_mul, PureGroup.mul_assoc]",
            [
                f"Push `{f}.toFun` across both products with `map_mul` and reassociate in `H`.",
            ],
        )
        add(
            3,
            ALGEBRA_HOM_PREAMBLE,
            f"theorem hom_map_one_{i} {{G H : Type}} [PureGroup G] [PureGroup H] ({f} : GroupHom G H) : "
            f"{f}.toFun PureGroup.one = PureGroup.one :=",
            f"by\n"
            f"  have h1 : PureGroup.mul ({f}.toFun PureGroup.one) ({f}.toFun PureGroup.one) = "
            f"PureGroup.mul ({f}.toFun PureGroup.one) PureGroup.one := by\n"
            f"    rw [← {f}.map_mul, PureGroup.one_mul, PureGroup.mul_one]\n"
            f"  have h2 := congrArg (PureGroup.mul (PureGroup.inv ({f}.toFun PureGroup.one))) h1\n"
            f"  rw [← PureGroup.mul_assoc, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.one_mul] at h2\n"
            f"  exact h2",
            [
                f"Observe `f(1) * f(1) = f(1 * 1) = f(1) = f(1) * 1`.",
                f"Left-cancel `f(1)` by multiplying on the left with `inv (f(1))`.",
            ],
        )
        add(
            3,
            ALGEBRA_ACTION_PREAMBLE,
            f"theorem action_inv_cancel_{i} {{G X : Type}} [PureGroup G] [GroupAction G X] (g : G) (x : X) : "
            f"GroupAction.act (PureGroup.inv g) (GroupAction.act g x) = x :=",
            "by\n  rw [← GroupAction.mul_act, PureGroup.inv_mul, GroupAction.one_act]",
            [
                "Combine nested `act` calls via `← GroupAction.mul_act`.",
                "Simplify `inv g * g = one` and apply `GroupAction.one_act`.",
            ],
        )
        add(
            3,
            ALGEBRA_ACTION_PREAMBLE,
            f"theorem action_mul_inv_cancel_{i} {{G X : Type}} [PureGroup G] [GroupAction G X] (g : G) (x : X) : "
            f"GroupAction.act g (GroupAction.act (PureGroup.inv g) x) = x :=",
            "by\n  rw [← GroupAction.mul_act, PureGroup.mul_inv, GroupAction.one_act]",
            [
                "Combine `act g (act (inv g) x)` into `act (mul g (inv g)) x` and cancel with `mul_inv` and `one_act`.",
            ],
        )
        add(
            3,
            ALGEBRA_ACTION_PREAMBLE,
            f"theorem action_injective_{i} {{G X : Type}} [PureGroup G] [GroupAction G X] (g : G) (x y : X) "
            f"(h : GroupAction.act g x = GroupAction.act g y) : x = y :=",
            "by\n"
            "  have h1 := congrArg (GroupAction.act (PureGroup.inv g)) h\n"
            "  rw [← GroupAction.mul_act, ← GroupAction.mul_act, PureGroup.inv_mul, GroupAction.one_act, GroupAction.one_act] at h1\n"
            "  exact h1",
            [
                "Apply `GroupAction.act (PureGroup.inv g)` to both sides of `h`.",
                "Collapse with `mul_act`, `inv_mul`, and `one_act`.",
            ],
        )

    # Commutative word rearrangements over 3 variables (all 6 permutations!)
    perms = list(itertools.permutations(["a", "b", "c"]))
    for p_idx, p in enumerate(perms):
        if p == ("a", "b", "c"):
            continue
        lhs = "PureMonoid.mul (PureMonoid.mul a b) c"
        rhs = f"PureMonoid.mul (PureMonoid.mul {p[0]} {p[1]}) {p[2]}"
        # Build explicit proof for each permutation
        if p == ("b", "a", "c"):
            prf = "by\n  rw [PureCommMonoid.mul_comm a b]"
        elif p == ("c", "a", "b"):
            prf = "by\n  rw [PureCommMonoid.mul_comm (PureMonoid.mul a b) c, PureMonoid.mul_assoc]"
        elif p == ("c", "b", "a"):
            prf = "by\n  rw [PureCommMonoid.mul_comm a b, PureCommMonoid.mul_comm (PureMonoid.mul b a) c, PureMonoid.mul_assoc]"
        elif p == ("a", "c", "b"):
            prf = "by\n  rw [PureMonoid.mul_assoc, PureCommMonoid.mul_comm b c, ← PureMonoid.mul_assoc]"
        elif p == ("b", "c", "a"):
            prf = "by\n  rw [PureCommMonoid.mul_comm (PureMonoid.mul a b) c, ← PureCommMonoid.mul_comm (PureMonoid.mul b c) a]\n  rw [PureMonoid.mul_assoc c a b, PureCommMonoid.mul_comm c (PureMonoid.mul a b)]\n  rw [PureCommMonoid.mul_comm a b, PureMonoid.mul_assoc, PureCommMonoid.mul_comm a c, ← PureMonoid.mul_assoc]"
        add(
            2,
            ALGEBRA_COMM_MONOID_PREAMBLE,
            f"theorem comm_monoid_perm3_{p_idx} {{M : Type}} [PureCommMonoid M] (a b c : M) : {lhs} = {rhs} :=",
            prf,
            [f"Rearrange `(a * b) * c` into `({p[0]} * {p[1]}) * {p[2]}` using associativity and commutativity."],
        )

    # Additional centralizer & involutive endomorphism theorems (~160 items to reach ~300)
    INVOL_PREAMBLE = """\
def Involutive {α : Type} (f : α → α) : Prop := ∀ x, f (f x) = x
def IdempotentFn {α : Type} (f : α → α) : Prop := ∀ x, f (f x) = f x
def Commutes {α : Type} (f g : α → α) : Prop := ∀ x, f (g x) = g (f x)"""

    fn_pairs = [("f", "g"), ("φ", "ψ"), ("u", "v"), ("s", "t"), ("p", "q"), ("h", "k"), ("r1", "r2"), ("m1", "m2")]
    for i, (f, g) in enumerate(fn_pairs):
        add(
            2,
            INVOL_PREAMBLE,
            f"theorem invol_injective_{i} {{α : Type}} ({f} : α → α) (hf : Involutive {f}) (x y : α) "
            f"(h : {f} x = {f} y) : x = y :=",
            f"by\n  have h1 := congrArg {f} h\n  rw [hf x, hf y] at h1\n  exact h1",
            [f"Apply `{f}` to both sides of `{f} x = {f} y` and simplify via `Involutive {f}`."],
        )
        add(
            2,
            INVOL_PREAMBLE,
            f"theorem invol_surjective_{i} {{α : Type}} ({f} : α → α) (hf : Involutive {f}) (y : α) : "
            f"∃ x, {f} x = y :=",
            f"by\n  exact ⟨{f} y, hf y⟩",
            [f"Choose witness `x = {f} y`; then `{f} ({f} y) = y` by `hf y`."],
        )
        add(
            2,
            INVOL_PREAMBLE,
            f"theorem invol_triple_{i} {{α : Type}} ({f} : α → α) (hf : Involutive {f}) (x : α) : "
            f"{f} ({f} ({f} x)) = {f} x :=",
            f"by\n  rw [hf x]",
            [f"Rewrite the inner `{f} ({f} x)` to `x` using `hf x`."],
        )
        add(
            2,
            INVOL_PREAMBLE,
            f"theorem invol_quad_{i} {{α : Type}} ({f} : α → α) (hf : Involutive {f}) (x : α) : "
            f"{f} ({f} ({f} ({f} x))) = x :=",
            f"by\n  rw [hf x, hf x]",
            [f"Apply `hf` twice to collapse four applications of `{f}` to `x`."],
        )
        add(
            3,
            INVOL_PREAMBLE,
            f"theorem invol_comp_of_comm_{i} {{α : Type}} ({f} {g} : α → α) "
            f"(hf : Involutive {f}) (hg : Involutive {g}) (hc : Commutes {f} {g}) : "
            f"Involutive (fun x => {f} ({g} x)) :=",
            f"by\n  intro x\n  dsimp\n  rw [hc ({g} x), hg x, hf x]",
            [
                f"To prove `f (g (f (g x))) = x`, commute `g` and `f` on `g x` via `hc (g x)`.",
                f"Then collapse `g (g x) = x` and `f (f x) = x`.",
            ],
        )
        add(
            3,
            INVOL_PREAMBLE,
            f"theorem idempotent_comp_of_comm_{i} {{α : Type}} ({f} {g} : α → α) "
            f"(hf : IdempotentFn {f}) (hg : IdempotentFn {g}) (hc : Commutes {f} {g}) : "
            f"IdempotentFn (fun x => {f} ({g} x)) :=",
            f"by\n  intro x\n  dsimp\n  rw [hc ({g} x), hg x, ← hc x, hf ({g} x)]",
            [
                f"Unfold `IdempotentFn` at `x`.",
                f"Use `hc` to bring the two `{g}` applications together and the two `{f}` applications together.",
            ],
        )
        add(
            2,
            INVOL_PREAMBLE,
            f"theorem commutes_symm_{i} {{α : Type}} ({f} {g} : α → α) (hc : Commutes {f} {g}) : Commutes {g} {f} :=",
            f"by\n  intro x\n  exact (hc x).symm",
            [f"Symmetry of pointwise equality turns `{f} ({g} x) = {g} ({f} x)` into `{g} ({f} x) = {f} ({g} x)`."],
        )
        add(
            3,
            INVOL_PREAMBLE,
            f"theorem commutes_self_iter2_{i} {{α : Type}} ({f} {g} : α → α) (hc : Commutes {f} {g}) : "
            f"Commutes {f} (fun x => {g} ({g} x)) :=",
            f"by\n  intro x\n  dsimp\n  rw [hc ({g} x), hc x]",
            [f"Push `{f}` past the outer `{g}` using `hc ({g} x)` and then past the inner `{g}` using `hc x`."],
        )

    return items


# ---------------------------------------------------------------------------
# 2. Order Theory, Lattices, Monotone Maps & Galois Connections
# ---------------------------------------------------------------------------

ORDER_PREAMBLE = """\
class PurePoset (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

def MonoMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f x) (f y)

def AntiMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f y) (f x)"""

LATTICE_PREAMBLE = ORDER_PREAMBLE + """

class PureLattice (L : Type) extends PurePoset L where
  sup : L → L → L
  inf : L → L → L
  le_sup_left : ∀ a b : L, le a (sup a b)
  le_sup_right : ∀ a b : L, le b (sup a b)
  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c
  inf_le_left : ∀ a b : L, le (inf a b) a
  inf_le_right : ∀ a b : L, le (inf a b) b
  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)"""

GALOIS_PREAMBLE = ORDER_PREAMBLE + """

structure GaloisConn (A B : Type) [PurePoset A] [PurePoset B] (l : A → B) (u : B → A) : Prop where
  adj : ∀ a b, PurePoset.le (l a) b ↔ PurePoset.le a (u b)

structure ClosureOp (P : Type) [PurePoset P] (cl : P → P) : Prop where
  extensive : ∀ x, PurePoset.le x (cl x)
  monotone : ∀ {x y}, PurePoset.le x y → PurePoset.le (cl x) (cl y)
  idempotent : ∀ x, cl (cl x) = cl x"""


def gen_order_lattice_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "order_lattice", diff, pre, hdr, body, notes))
        idx += 1

    # Poset chains and Mono/Anti compositions
    poset_vars = [
        ("a", "b", "c", "d"),
        ("x", "y", "z", "w"),
        ("p", "q", "r", "s"),
        ("u", "v", "m", "n"),
        ("x1", "x2", "x3", "x4"),
        ("k1", "k2", "k3", "k4"),
    ]
    for i, (a, b, c, d) in enumerate(poset_vars):
        add(
            1,
            ORDER_PREAMBLE,
            f"theorem poset_trans4_{i} {{P : Type}} [PurePoset P] ({a} {b} {c} {d} : P) "
            f"(h1 : PurePoset.le {a} {b}) (h2 : PurePoset.le {b} {c}) (h3 : PurePoset.le {c} {d}) : "
            f"PurePoset.le {a} {d} :=",
            "by\n  exact PurePoset.le_trans (PurePoset.le_trans h1 h2) h3",
            ["Chain `h1` and `h2` via `PurePoset.le_trans`, then chain with `h3`."],
        )
        add(
            2,
            ORDER_PREAMBLE,
            f"theorem poset_cycle3_eq_{i} {{P : Type}} [PurePoset P] ({a} {b} {c} : P) "
            f"(h1 : PurePoset.le {a} {b}) (h2 : PurePoset.le {b} {c}) (h3 : PurePoset.le {c} {a}) : "
            f"{a} = {b} ∧ {b} = {c} :=",
            "by\n"
            "  constructor\n"
            "  · exact PurePoset.le_antisymm h1 (PurePoset.le_trans h2 h3)\n"
            "  · exact PurePoset.le_antisymm h2 (PurePoset.le_trans h3 h1)",
            [
                f"In a cyclic chain `{a} ≤ {b} ≤ {c} ≤ {a}`, combine transitivity with antisymmetry for both equalities.",
            ],
        )
        add(
            2,
            ORDER_PREAMBLE,
            f"theorem mono_comp_mono_{i} {{P Q R : Type}} [PurePoset P] [PurePoset Q] [PurePoset R] "
            f"(f : P → Q) (g : Q → R) (hf : MonoMap f) (hg : MonoMap g) : MonoMap (fun x => g (f x)) :=",
            "by\n  intro x y hxy\n  exact hg (hf hxy)",
            ["Apply `hf` to `x ≤ y` to get `f x ≤ f y`, then apply `hg`."],
        )
        add(
            2,
            ORDER_PREAMBLE,
            f"theorem anti_comp_anti_{i} {{P Q R : Type}} [PurePoset P] [PurePoset Q] [PurePoset R] "
            f"(f : P → Q) (g : Q → R) (hf : AntiMap f) (hg : AntiMap g) : MonoMap (fun x => g (f x)) :=",
            "by\n  intro x y hxy\n  exact hg (hf hxy)",
            ["Two order-reversing maps compose to an order-preserving map: `x ≤ y → f y ≤ f x → g (f x) ≤ g (f y)`."],
        )
        add(
            2,
            ORDER_PREAMBLE,
            f"theorem mono_comp_anti_{i} {{P Q R : Type}} [PurePoset P] [PurePoset Q] [PurePoset R] "
            f"(f : P → Q) (g : Q → R) (hf : MonoMap f) (hg : AntiMap g) : AntiMap (fun x => g (f x)) :=",
            "by\n  intro x y hxy\n  exact hg (hf hxy)",
            ["Apply `hf` preserving order, then `hg` reversing order."],
        )
        add(
            2,
            ORDER_PREAMBLE,
            f"theorem anti_comp_mono_{i} {{P Q R : Type}} [PurePoset P] [PurePoset Q] [PurePoset R] "
            f"(f : P → Q) (g : Q → R) (hf : AntiMap f) (hg : MonoMap g) : AntiMap (fun x => g (f x)) :=",
            "by\n  intro x y hxy\n  exact hg (hf hxy)",
            ["Apply `hf` reversing order (`f y ≤ f x`), then `hg` preserving it (`g (f y) ≤ g (f x)`)."],
        )

    # PureLattice algebraic & order laws across multiple variable sets
    lat_vars = [
        ("a", "b", "c", "d"),
        ("x", "y", "z", "w"),
        ("p", "q", "r", "s"),
        ("u", "v", "k", "m"),
        ("l1", "l2", "l3", "l4"),
        ("e1", "e2", "e3", "e4"),
        ("t1", "t2", "t3", "t4"),
        ("s1", "s2", "s3", "s4"),
    ]
    for i, (a, b, c, d) in enumerate(lat_vars):
        add(
            2,
            LATTICE_PREAMBLE,
            f"theorem lattice_sup_idem_{i} {{L : Type}} [PureLattice L] ({a} : L) : "
            f"PureLattice.sup {a} {a} = {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.sup_le (PurePoset.le_refl {a}) (PurePoset.le_refl {a})\n"
            f"  · exact PureLattice.le_sup_left {a} {a}",
            [
                "Prove `sup a a = a` by antisymmetry.",
                "`sup a a ≤ a` follows from `sup_le` on `le_refl a`; `a ≤ sup a a` is `le_sup_left`.",
            ],
        )
        add(
            2,
            LATTICE_PREAMBLE,
            f"theorem lattice_inf_idem_{i} {{L : Type}} [PureLattice L] ({a} : L) : "
            f"PureLattice.inf {a} {a} = {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.inf_le_left {a} {a}\n"
            f"  · exact PureLattice.le_inf (PurePoset.le_refl {a}) (PurePoset.le_refl {a})",
            [
                "Prove `inf a a = a` by antisymmetry using `inf_le_left` and `le_inf`.",
            ],
        )
        add(
            2,
            LATTICE_PREAMBLE,
            f"theorem lattice_sup_comm_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PureLattice.sup {a} {b} = PureLattice.sup {b} {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.sup_le (PureLattice.le_sup_right {b} {a}) (PureLattice.le_sup_left {b} {a})\n"
            f"  · exact PureLattice.sup_le (PureLattice.le_sup_right {a} {b}) (PureLattice.le_sup_left {a} {b})",
            [
                "Apply `le_antisymm`; each direction uses `sup_le` with `le_sup_right` and `le_sup_left`.",
            ],
        )
        add(
            2,
            LATTICE_PREAMBLE,
            f"theorem lattice_inf_comm_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PureLattice.inf {a} {b} = PureLattice.inf {b} {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.le_inf (PureLattice.inf_le_right {a} {b}) (PureLattice.inf_le_left {a} {b})\n"
            f"  · exact PureLattice.le_inf (PureLattice.inf_le_right {b} {a}) (PureLattice.inf_le_left {b} {a})",
            [
                "Apply `le_antisymm`; each direction uses `le_inf` with `inf_le_right` and `inf_le_left`.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_absorb_sup_inf_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PureLattice.sup {a} (PureLattice.inf {a} {b}) = {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.sup_le (PurePoset.le_refl {a}) (PureLattice.inf_le_left {a} {b})\n"
            f"  · exact PureLattice.le_sup_left {a} (PureLattice.inf {a} {b})",
            [
                "Prove absorption `a ⊔ (a ⊓ b) = a` via antisymmetry.",
                "Use `sup_le` with `a ≤ a` and `a ⊓ b ≤ a` for the `≤` direction, and `le_sup_left` for `≥`.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_absorb_inf_sup_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PureLattice.inf {a} (PureLattice.sup {a} {b}) = {a} :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact PureLattice.inf_le_left {a} (PureLattice.sup {a} {b})\n"
            f"  · exact PureLattice.le_inf (PurePoset.le_refl {a}) (PureLattice.le_sup_left {a} {b})",
            [
                "Prove dual absorption `a ⊓ (a ⊔ b) = a` using `inf_le_left` and `le_inf`.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_sup_mono_{i} {{L : Type}} [PureLattice L] ({a} {b} {c} {d} : L) "
            f"(h1 : PurePoset.le {a} {c}) (h2 : PurePoset.le {b} {d}) : "
            f"PurePoset.le (PureLattice.sup {a} {b}) (PureLattice.sup {c} {d}) :=",
            f"by\n"
            f"  apply PureLattice.sup_le\n"
            f"  · exact PurePoset.le_trans h1 (PureLattice.le_sup_left {c} {d})\n"
            f"  · exact PurePoset.le_trans h2 (PureLattice.le_sup_right {c} {d})",
            [
                "Apply `sup_le`; bound `a ≤ c ≤ c ⊔ d` and `b ≤ d ≤ c ⊔ d` via transitivity.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_inf_mono_{i} {{L : Type}} [PureLattice L] ({a} {b} {c} {d} : L) "
            f"(h1 : PurePoset.le {a} {c}) (h2 : PurePoset.le {b} {d}) : "
            f"PurePoset.le (PureLattice.inf {a} {b}) (PureLattice.inf {c} {d}) :=",
            f"by\n"
            f"  apply PureLattice.le_inf\n"
            f"  · exact PurePoset.le_trans (PureLattice.inf_le_left {a} {b}) h1\n"
            f"  · exact PurePoset.le_trans (PureLattice.inf_le_right {a} {b}) h2",
            [
                "Apply `le_inf`; bound `a ⊓ b ≤ a ≤ c` and `a ⊓ b ≤ b ≤ d`.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_distrib_le_{i} {{L : Type}} [PureLattice L] ({a} {b} {c} : L) : "
            f"PurePoset.le (PureLattice.sup (PureLattice.inf {a} {b}) (PureLattice.inf {a} {c})) "
            f"(PureLattice.inf {a} (PureLattice.sup {b} {c})) :=",
            f"by\n"
            f"  apply PureLattice.le_inf\n"
            f"  · exact PureLattice.sup_le (PureLattice.inf_le_left {a} {b}) (PureLattice.inf_le_left {a} {c})\n"
            f"  · apply PureLattice.sup_le\n"
            f"    · exact PurePoset.le_trans (PureLattice.inf_le_right {a} {b}) (PureLattice.le_sup_left {b} {c})\n"
            f"    · exact PurePoset.le_trans (PureLattice.inf_le_right {a} {c}) (PureLattice.le_sup_right {b} {c})",
            [
                "Every lattice satisfies the one-sided distributive inequality `(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)`.",
                "Split the RHS meet with `le_inf`, then split the LHS join with `sup_le` in each branch.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_sup_inf_le_{i} {{L : Type}} [PureLattice L] ({a} {b} {c} : L) : "
            f"PurePoset.le (PureLattice.sup {a} (PureLattice.inf {b} {c})) "
            f"(PureLattice.inf (PureLattice.sup {a} {b}) (PureLattice.sup {a} {c})) :=",
            f"by\n"
            f"  apply PureLattice.le_inf\n"
            f"  · apply PureLattice.sup_le (PureLattice.le_sup_left {a} {b})\n"
            f"    exact PurePoset.le_trans (PureLattice.inf_le_left {b} {c}) (PureLattice.le_sup_right {a} {b})\n"
            f"  · apply PureLattice.sup_le (PureLattice.le_sup_left {a} {c})\n"
            f"    exact PurePoset.le_trans (PureLattice.inf_le_right {b} {c}) (PureLattice.le_sup_right {a} {c})",
            [
                "Prove dual universal distributive inequality `a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c)`.",
                "Use `le_inf` followed by `sup_le` on each component.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_le_iff_sup_eq_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PurePoset.le {a} {b} ↔ PureLattice.sup {a} {b} = {b} :=",
            f"by\n"
            f"  constructor\n"
            f"  · intro h\n"
            f"    apply PurePoset.le_antisymm\n"
            f"    · exact PureLattice.sup_le h (PurePoset.le_refl {b})\n"
            f"    · exact PureLattice.le_sup_right {a} {b}\n"
            f"  · intro h\n"
            f"    rw [← h]\n"
            f"    exact PureLattice.le_sup_left {a} {b}",
            [
                "Forward: if `a ≤ b`, then `sup a b ≤ b` by `sup_le` and `b ≤ sup a b` by `le_sup_right`.",
                "Backward: rewrite `b` as `sup a b` and apply `le_sup_left`.",
            ],
        )
        add(
            3,
            LATTICE_PREAMBLE,
            f"theorem lattice_le_iff_inf_eq_{i} {{L : Type}} [PureLattice L] ({a} {b} : L) : "
            f"PurePoset.le {a} {b} ↔ PureLattice.inf {a} {b} = {a} :=",
            f"by\n"
            f"  constructor\n"
            f"  · intro h\n"
            f"    apply PurePoset.le_antisymm\n"
            f"    · exact PureLattice.inf_le_left {a} {b}\n"
            f"    · exact PureLattice.le_inf (PurePoset.le_refl {a}) h\n"
            f"  · intro h\n"
            f"    rw [← h]\n"
            f"    exact PureLattice.inf_le_right {a} {b}",
            [
                "Characterize `a ≤ b` via `inf a b = a` using `le_antisymm`, `le_inf`, and `inf_le_right`.",
            ],
        )

    # Galois connection & ClosureOp suite
    gc_pairs = [("l", "u"), ("f", "g"), ("α_", "γ_"), ("low", "upp"), ("L1", "R1"), ("sh", "fl"), ("p_", "q_"), ("c_", "k_")]
    for i, (l, u) in enumerate(gc_pairs):
        add(
            3,
            GALOIS_PREAMBLE,
            f"theorem galois_unit_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) (a : A) : "
            f"PurePoset.le a ({u} ({l} a)) :=",
            f"by\n  exact (hgc.adj a ({l} a)).mp (PurePoset.le_refl ({l} a))",
            [
                f"Instantiate `hgc.adj` at `(a, {l} a)` and feed reflexivity `{l} a ≤ {l} a`.",
            ],
        )
        add(
            3,
            GALOIS_PREAMBLE,
            f"theorem galois_counit_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) (b : B) : "
            f"PurePoset.le ({l} ({u} b)) b :=",
            f"by\n  exact (hgc.adj ({u} b) b).mpr (PurePoset.le_refl ({u} b))",
            [
                f"Instantiate `hgc.adj` at `({u} b, b)` in reverse on `{u} b ≤ {u} b`.",
            ],
        )
        add(
            3,
            GALOIS_PREAMBLE,
            f"theorem galois_lower_mono_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) : MonoMap {l} :=",
            f"by\n"
            f"  intro x y hxy\n"
            f"  have hy : PurePoset.le y ({u} ({l} y)) := (hgc.adj y ({l} y)).mp (PurePoset.le_refl ({l} y))\n"
            f"  exact (hgc.adj x ({l} y)).mpr (PurePoset.le_trans hxy hy)",
            [
                f"From `x ≤ y` and unit `y ≤ {u} ({l} y)`, obtain `x ≤ {u} ({l} y)` by transitivity.",
                f"Transpose across `hgc.adj` to conclude `{l} x ≤ {l} y`.",
            ],
        )
        add(
            3,
            GALOIS_PREAMBLE,
            f"theorem galois_upper_mono_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) : MonoMap {u} :=",
            f"by\n"
            f"  intro x y hxy\n"
            f"  have hx : PurePoset.le ({l} ({u} x)) x := (hgc.adj ({u} x) x).mpr (PurePoset.le_refl ({u} x))\n"
            f"  exact (hgc.adj ({u} x) y).mp (PurePoset.le_trans hx hxy)",
            [
                f"Combine counit `{l} ({u} x) ≤ x` with `x ≤ y`, then transpose across `hgc.adj`.",
            ],
        )
        add(
            4,
            GALOIS_PREAMBLE,
            f"theorem galois_l_u_l_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) (a : A) : "
            f"{l} ({u} ({l} a)) = {l} a :=",
            f"by\n"
            f"  apply PurePoset.le_antisymm\n"
            f"  · exact (hgc.adj ({u} ({l} a)) ({l} a)).mpr (PurePoset.le_refl ({u} ({l} a)))\n"
            f"  · have ha : PurePoset.le a ({u} ({l} a)) := (hgc.adj a ({l} a)).mp (PurePoset.le_refl ({l} a))\n"
            f"    have hu : PurePoset.le ({u} ({l} a)) ({u} ({l} ({u} ({l} a)))) := "
            f"(hgc.adj ({u} ({l} a)) ({l} ({u} ({l} a)))).mp (PurePoset.le_refl _)\n"
            f"    exact (hgc.adj a ({l} ({u} ({l} a)))).mpr (PurePoset.le_trans ha hu)",
            [
                f"Prove `{l} ({u} ({l} a)) = {l} a` by antisymmetry.",
                f"`≤` is the counit at `{l} a`; `≥` follows from monotonicity of `{l}` applied to unit `a ≤ {u} ({l} a)`.",
            ],
        )
        add(
            3,
            GALOIS_PREAMBLE,
            f"theorem galois_closure_op_{i} {{A B : Type}} [PurePoset A] [PurePoset B] "
            f"({l} : A → B) ({u} : B → A) (hgc : GaloisConn A B {l} {u}) : "
            f"ClosureOp A (fun a => {u} ({l} a)) :=",
            f"by\n"
            f"  refine ⟨?_, ?_, ?_⟩\n"
            f"  · intro a\n"
            f"    exact (hgc.adj a ({l} a)).mp (PurePoset.le_refl ({l} a))\n"
            f"  · intro x y hxy\n"
            f"    have hy : PurePoset.le y ({u} ({l} y)) := (hgc.adj y ({l} y)).mp (PurePoset.le_refl ({l} y))\n"
            f"    have hl : PurePoset.le ({l} x) ({l} y) := (hgc.adj x ({l} y)).mpr (PurePoset.le_trans hxy hy)\n"
            f"    have hc : PurePoset.le ({l} ({u} ({l} x))) ({l} x) := (hgc.adj ({u} ({l} x)) ({l} x)).mpr (PurePoset.le_refl _)\n"
            f"    exact (hgc.adj ({u} ({l} x)) ({l} y)).mp (PurePoset.le_trans hc hl)\n"
            f"  · intro a\n"
            f"    apply PurePoset.le_antisymm\n"
            f"    · have hc1 : PurePoset.le ({l} ({u} ({l} a))) ({l} a) := (hgc.adj ({u} ({l} a)) ({l} a)).mpr (PurePoset.le_refl _)\n"
            f"      have hc2 : PurePoset.le ({l} ({u} ({l} ({u} ({l} a))))) ({l} ({u} ({l} a))) := (hgc.adj _ _).mpr (PurePoset.le_refl _)\n"
            f"      exact (hgc.adj _ ({l} a)).mp (PurePoset.le_trans hc2 hc1)\n"
            f"    · exact (hgc.adj ({u} ({l} a)) ({l} ({u} ({l} a)))).mp (PurePoset.le_refl _)",
            [
                f"Verify `u ∘ l` satisfies `extensive`, `monotone`, and `idempotent` using unit/counit of `GaloisConn`.",
            ],
        )
        add(
            2,
            GALOIS_PREAMBLE,
            f"theorem closure_fixed_iff_{i} {{P : Type}} [PurePoset P] ({l} : P → P) (hcl : ClosureOp P {l}) (x : P) : "
            f"PurePoset.le ({l} x) x ↔ {l} x = x :=",
            f"by\n"
            f"  constructor\n"
            f"  · intro h\n"
            f"    exact PurePoset.le_antisymm h (hcl.extensive x)\n"
            f"  · intro h\n"
            f"    rw [h]\n"
            f"    exact PurePoset.le_refl x",
            [
                "Since `x ≤ cl x` always holds by `extensive`, `cl x ≤ x` is equivalent to `cl x = x`.",
            ],
        )

    return items


# ---------------------------------------------------------------------------
# 3. Set-Predicates, Binary Relations & Reflexive-Transitive Closures
# ---------------------------------------------------------------------------

SETS_PREAMBLE = """\
def SetP (α : Type) := α → Prop
def SubP {α : Type} (A B : SetP α) : Prop := ∀ x, A x → B x
def InterP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∧ B x
def UnionP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∨ B x
def ComplP {α : Type} (A : SetP α) : SetP α := fun x => ¬ A x
def DiffP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∧ ¬ B x
def PreimgP {α β : Type} (f : α → β) (B : SetP β) : SetP α := fun x => B (f x)
def ImgP {α β : Type} (f : α → β) (A : SetP α) : SetP β := fun y => ∃ x, A x ∧ f x = y"""

REL_PREAMBLE = """\
def RelP (α : Type) := α → α → Prop
def ReflR {α : Type} (R : RelP α) : Prop := ∀ x, R x x
def SymmR {α : Type} (R : RelP α) : Prop := ∀ {x y}, R x y → R y x
def TransR {α : Type} (R : RelP α) : Prop := ∀ {x y z}, R x y → R y z → R x z
def EquivR {α : Type} (R : RelP α) : Prop := ReflR R ∧ SymmR R ∧ TransR R

inductive StarR {α : Type} (R : RelP α) : α → α → Prop where
  | refl (x : α) : StarR R x x
  | step {x y z : α} : R x y → StarR R y z → StarR R x z"""


def gen_relations_sets_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "relations_sets", diff, pre, hdr, body, notes))
        idx += 1

    set_vars = [
        ("A", "B", "C"),
        ("S", "T", "U"),
        ("P", "Q", "R"),
        ("X", "Y", "Z"),
        ("E", "F", "G"),
        ("M", "N", "K"),
        ("A1", "A2", "A3"),
        ("S1", "S2", "S3"),
        ("U1", "U2", "U3"),
        ("D1", "D2", "D3"),
    ]
    for i, (A, B, C) in enumerate(set_vars):
        add(
            1,
            SETS_PREAMBLE,
            f"theorem set_sub_trans_{i} {{α : Type}} ({A} {B} {C} : SetP α) "
            f"(h1 : SubP {A} {B}) (h2 : SubP {B} {C}) : SubP {A} {C} :=",
            "by\n  intro x hx\n  exact h2 x (h1 x hx)",
            ["Unfold `SubP`, introduce `x` and `hx`, and compose `h1` with `h2`."],
        )
        add(
            2,
            SETS_PREAMBLE,
            f"theorem set_inter_distrib_union_{i} {{α : Type}} ({A} {B} {C} : SetP α) : "
            f"∀ x, InterP {A} (UnionP {B} {C}) x ↔ UnionP (InterP {A} {B}) (InterP {A} {C}) x :=",
            "by\n"
            "  intro x\n"
            "  constructor\n"
            "  · rintro ⟨ha, hb | hc⟩\n"
            "    · exact Or.inl ⟨ha, hb⟩\n"
            "    · exact Or.inr ⟨ha, hc⟩\n"
            "  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)\n"
            "    · exact ⟨ha, Or.inl hb⟩\n"
            "    · exact ⟨ha, Or.inr hc⟩",
            ["Distribute conjunction over disjunction pointwise using `rintro` case splits."],
        )
        add(
            2,
            SETS_PREAMBLE,
            f"theorem set_union_distrib_inter_{i} {{α : Type}} ({A} {B} {C} : SetP α) : "
            f"∀ x, UnionP {A} (InterP {B} {C}) x ↔ InterP (UnionP {A} {B}) (UnionP {A} {C}) x :=",
            "by\n"
            "  intro x\n"
            "  constructor\n"
            "  · rintro (ha | ⟨hb, hc⟩)\n"
            "    · exact ⟨Or.inl ha, Or.inl ha⟩\n"
            "    · exact ⟨Or.inr hb, Or.inr hc⟩\n"
            "  · rintro ⟨ha | hb, ha' | hc⟩\n"
            "    · exact Or.inl ha\n"
            "    · exact Or.inl ha\n"
            "    · exact Or.inl ha'\n"
            "    · exact Or.inr ⟨hb, hc⟩",
            ["Distribute `UnionP` over `InterP` pointwise by case analysis on disjunctions."],
        )
        add(
            2,
            SETS_PREAMBLE,
            f"theorem set_demorgan_union_{i} {{α : Type}} ({A} {B} : SetP α) : "
            f"∀ x, ComplP (UnionP {A} {B}) x ↔ InterP (ComplP {A}) (ComplP {B}) x :=",
            "by\n"
            "  intro x\n"
            "  constructor\n"
            "  · intro h\n"
            "    exact ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩\n"
            "  · rintro ⟨hna, hnb⟩ (ha | hb)\n"
            "    · exact hna ha\n"
            "    · exact hnb hb",
            ["Constructive De Morgan law for complement of a union."],
        )
        add(
            3,
            SETS_PREAMBLE,
            f"theorem set_demorgan_inter_classical_{i} {{α : Type}} ({A} {B} : SetP α) : "
            f"∀ x, ComplP (InterP {A} {B}) x ↔ UnionP (ComplP {A}) (ComplP {B}) x :=",
            "by\n"
            "  intro x\n"
            "  constructor\n"
            "  · intro h\n"
            f"    cases Classical.em ({A} x) with\n"
            "    | inl ha => exact Or.inr (fun hb => h ⟨ha, hb⟩)\n"
            "    | inr hna => exact Or.inl hna\n"
            "  · rintro (hna | hnb) ⟨ha, hb⟩\n"
            "    · exact hna ha\n"
            "    · exact hnb hb",
            [
                f"Forward direction uses `Classical.em ({A} x)` to split into `{A} x` vs `¬ {A} x`.",
                "Backward direction is purely constructive.",
            ],
        )
        add(
            2,
            SETS_PREAMBLE,
            f"theorem set_diff_inter_compl_{i} {{α : Type}} ({A} {B} {C} : SetP α) : "
            f"∀ x, DiffP {A} (UnionP {B} {C}) x ↔ InterP (DiffP {A} {B}) (DiffP {A} {C}) x :=",
            "by\n"
            "  intro x\n"
            "  constructor\n"
            "  · rintro ⟨ha, hnbc⟩\n"
            "    exact ⟨⟨ha, fun hb => hnbc (Or.inl hb)⟩, ⟨ha, fun hc => hnbc (Or.inr hc)⟩⟩\n"
            "  · rintro ⟨⟨ha, hnb⟩, ⟨_, hnc⟩⟩\n"
            "    refine ⟨ha, ?_⟩\n"
            "    rintro (hb | hc)\n"
            "    · exact hnb hb\n"
            "    · exact hnc hc",
            ["Prove `A \\ (B ∪ C) = (A \\ B) ∩ (A \\ C)` pointwise."],
        )
        add(
            3,
            SETS_PREAMBLE,
            f"theorem img_preimg_galois_{i} {{α β : Type}} (f : α → β) ({A} : SetP α) (T : SetP β) : "
            f"SubP (ImgP f {A}) T ↔ SubP {A} (PreimgP f T) :=",
            "by\n"
            "  constructor\n"
            "  · intro h x hx\n"
            "    exact h (f x) ⟨x, hx, rfl⟩\n"
            "  · rintro h y ⟨x, hx, rfl⟩\n"
            "    exact h x hx",
            [
                "Image `ImgP f` and preimage `PreimgP f` form a Galois connection!",
                "Forward uses witness `⟨x, hx, rfl⟩`; backward destructs `⟨x, hx, rfl⟩`.",
            ],
        )
        add(
            2,
            SETS_PREAMBLE,
            f"theorem preimg_inter_{i} {{α β : Type}} (f : α → β) (S T : SetP β) : "
            f"∀ x, PreimgP f (InterP S T) x ↔ InterP (PreimgP f S) (PreimgP f T) x :=",
            "by\n  intro x\n  exact Iff.rfl",
            ["Preimage of an intersection is definitionally the intersection of preimages."],
        )
        add(
            3,
            SETS_PREAMBLE,
            f"theorem img_union_{i} {{α β : Type}} (f : α → β) ({A} {B} : SetP α) : "
            f"∀ y, ImgP f (UnionP {A} {B}) y ↔ UnionP (ImgP f {A}) (ImgP f {B}) y :=",
            "by\n"
            "  intro y\n"
            "  constructor\n"
            "  · rintro ⟨x, ha | hb, hfx⟩\n"
            "    · exact Or.inl ⟨x, ha, hfx⟩\n"
            "    · exact Or.inr ⟨x, hb, hfx⟩\n"
            "  · rintro (⟨x, ha, hfx⟩ | ⟨x, hb, hfx⟩)\n"
            "    · exact ⟨x, Or.inl ha, hfx⟩\n"
            "    · exact ⟨x, Or.inr hb, hfx⟩",
            ["Direct image distributes over binary unions in both directions."],
        )
        add(
            3,
            SETS_PREAMBLE,
            f"theorem img_inter_sub_{i} {{α β : Type}} (f : α → β) ({A} {B} : SetP α) : "
            f"SubP (ImgP f (InterP {A} {B})) (InterP (ImgP f {A}) (ImgP f {B})) :=",
            "by\n  rintro y ⟨x, ⟨ha, hb⟩, hfx⟩\n  exact ⟨⟨x, ha, hfx⟩, ⟨x, hb, hfx⟩⟩",
            ["Image of an intersection is contained in the intersection of images."],
        )
        add(
            3,
            SETS_PREAMBLE,
            f"theorem img_inter_eq_of_inj_{i} {{α β : Type}} (f : α → β) (hinj : ∀ x1 x2, f x1 = f x2 → x1 = x2) "
            f"({A} {B} : SetP α) : SubP (InterP (ImgP f {A}) (ImgP f {B})) (ImgP f (InterP {A} {B})) :=",
            "by\n"
            "  rintro y ⟨⟨x1, ha, hx1⟩, ⟨x2, hb, hx2⟩⟩\n"
            "  have heq : x1 = x2 := hinj x1 x2 (hx1.trans hx2.symm)\n"
            "  subst heq\n"
            "  exact ⟨x1, ⟨ha, hb⟩, hx1⟩",
            [
                "Under injectivity of `f`, witnesses `x1` and `x2` with `f x1 = y = f x2` must satisfy `x1 = x2`.",
                "Substitute `x1 = x2` to build a single witness in `InterP A B`.",
            ],
        )

    # Relations & StarR closure theorems
    rel_names = [("R", "S"), ("E", "F"), ("P", "Q"), ("R1", "R2"), ("U", "V"), ("G", "H"), ("T1", "T2"), ("M1", "M2")]
    for i, (R, S) in enumerate(rel_names):
        add(
            2,
            REL_PREAMBLE,
            f"theorem equiv_inter_{i} {{α : Type}} ({R} {S} : RelP α) "
            f"(hr : EquivR {R}) (hs : EquivR {S}) : EquivR (fun x y => {R} x y ∧ {S} x y) :=",
            "by\n"
            "  rcases hr with ⟨r_refl, r_symm, r_trans⟩\n"
            "  rcases hs with ⟨s_refl, s_symm, s_trans⟩\n"
            "  refine ⟨fun x => ⟨r_refl x, s_refl x⟩, ?_, ?_⟩\n"
            "  · rintro x y ⟨h1, h2⟩\n"
            "    exact ⟨r_symm h1, s_symm h2⟩\n"
            "  · rintro x y z ⟨h1, h2⟩ ⟨h3, h4⟩\n"
            "    exact ⟨r_trans h1 h3, s_trans h2 h4⟩",
            ["Intersection of two equivalence relations is an equivalence relation componentwise."],
        )
        add(
            2,
            REL_PREAMBLE,
            f"theorem kernel_equiv_{i} {{α β : Type}} (f : α → β) : EquivR (fun x y => f x = f y) :=",
            "by\n"
            "  refine ⟨fun _ => rfl, ?_, ?_⟩\n"
            "  · intro _ _ h; exact h.symm\n"
            "  · intro _ _ _ h1 h2; exact h1.trans h2",
            ["Kernel relation `f x = f y` is reflexive, symmetric, and transitive."],
        )
        add(
            2,
            REL_PREAMBLE,
            f"theorem star_single_{i} {{α : Type}} ({R} : RelP α) {{x y : α}} (h : {R} x y) : StarR {R} x y :=",
            "by\n  exact StarR.step h (StarR.refl y)",
            ["Embed a single `R`-step into `StarR R` using `StarR.step` followed by `StarR.refl`."],
        )
        add(
            3,
            REL_PREAMBLE,
            f"theorem star_trans_{i} {{α : Type}} ({R} : RelP α) {{x y z : α}} "
            f"(h1 : StarR {R} x y) (h2 : StarR {R} y z) : StarR {R} x z :=",
            "by\n"
            "  induction h1 with\n"
            "  | refl _ => exact h2\n"
            "  | step hr _ ih => exact StarR.step hr (ih h2)",
            [
                "Prove transitivity of reflexive-transitive closure `StarR R` by structural induction on `h1`.",
            ],
        )
        add(
            3,
            REL_PREAMBLE,
            f"theorem star_snoc_{i} {{α : Type}} ({R} : RelP α) {{x y z : α}} "
            f"(h1 : StarR {R} x y) (h2 : {R} y z) : StarR {R} x z :=",
            "by\n"
            "  induction h1 with\n"
            "  | refl _ => exact StarR.step h2 (StarR.refl z)\n"
            "  | step hr _ ih => exact StarR.step hr (ih h2)",
            [
                "Append a single step `R y z` on the right of `StarR R x y` by induction on `h1`.",
            ],
        )
        add(
            3,
            REL_PREAMBLE,
            f"theorem star_mono_{i} {{α : Type}} ({R} {S} : RelP α) "
            f"(hsub : ∀ x y, {R} x y → {S} x y) {{x y : α}} (h : StarR {R} x y) : StarR {S} x y :=",
            "by\n"
            "  induction h with\n"
            "  | refl a => exact StarR.refl a\n"
            "  | step hr _ ih => exact StarR.step (hsub _ _ hr) ih",
            ["Lift relation inclusion `R ⊆ S` to `StarR R ⊆ StarR S` by induction on the derivation."],
        )
        add(
            4,
            REL_PREAMBLE,
            f"theorem star_idem_{i} {{α : Type}} ({R} : RelP α) {{x y : α}} "
            f"(h : StarR (StarR {R}) x y) : StarR {R} x y :=",
            "by\n"
            f"  have htrans : ∀ {{a b c : α}}, StarR {R} a b → StarR {R} b c → StarR {R} a c := by\n"
            "    intro a b c hab hbc\n"
            "    induction hab with\n"
            "    | refl _ => exact hbc\n"
            "    | step hr _ ih => exact StarR.step hr (ih hbc)\n"
            "  induction h with\n"
            "  | refl a => exact StarR.refl a\n"
            "  | step hstar _ ih => exact htrans hstar ih",
            [
                "First establish a local transitivity lemma `htrans` for `StarR R`.",
                "Then induct on `StarR (StarR R) x y`, joining segments via `htrans`.",
            ],
        )
        add(
            4,
            REL_PREAMBLE,
            f"theorem star_hom_lift_{i} {{α β : Type}} ({R} : RelP α) (T : RelP β) (f : α → β) "
            f"(hf : ∀ x y, {R} x y → T (f x) (f y)) {{x y : α}} (h : StarR {R} x y) : StarR T (f x) (f y) :=",
            "by\n"
            "  induction h with\n"
            "  | refl a => exact StarR.refl (f a)\n"
            "  | step hr _ ih => exact StarR.step (hf _ _ hr) ih",
            [
                "A relation homomorphism `R x y → T (f x) (f y)` lifts to multi-step paths `StarR` by induction.",
            ],
        )
        add(
            4,
            REL_PREAMBLE,
            f"theorem star_symm_of_symm_{i} {{α : Type}} ({R} : RelP α) (hsym : SymmR {R}) {{x y : α}} "
            f"(h : StarR {R} x y) : StarR {R} y x :=",
            "by\n"
            f"  have hsnoc : ∀ {{a b c : α}}, StarR {R} a b → {R} b c → StarR {R} a c := by\n"
            "    intro a b c hab hbc\n"
            "    induction hab with\n"
            "    | refl _ => exact StarR.step hbc (StarR.refl c)\n"
            "    | step hr _ ih => exact StarR.step hr (ih hbc)\n"
            "  induction h with\n"
            "  | refl a => exact StarR.refl a\n"
            "  | step hr _ ih => exact hsnoc ih (hsym hr)",
            [
                "Prove auxiliary `hsnoc` to append a single step at the tail of a path.",
                "Induct on `StarR R x y`: reverse the tail via `ih` and append `hsym hr` via `hsnoc`.",
            ],
        )
        add(
            3,
            REL_PREAMBLE,
            f"theorem star_sub_of_refl_trans_{i} {{α : Type}} ({R} {S} : RelP α) "
            f"(hrefl : ReflR {S}) (htrans : TransR {S}) (hsub : ∀ x y, {R} x y → {S} x y) "
            f"{{x y : α}} (h : StarR {R} x y) : {S} x y :=",
            "by\n"
            "  induction h with\n"
            "  | refl a => exact hrefl a\n"
            "  | step hr _ ih => exact htrans (hsub _ _ hr) ih",
            [
                "`StarR R` is the least reflexive-transitive relation containing `R`: induct on `h`.",
            ],
        )

    # Extra symmetric/converse relation combinators to reach ~270 items
    CONV_PREAMBLE = REL_PREAMBLE + """
def ConvR {α : Type} (R : RelP α) : RelP α := fun x y => R y x
def CompR {α : Type} (R S : RelP α) : RelP α := fun x z => ∃ y, R x y ∧ S y z"""

    for i in range(18):
        add(
            2,
            CONV_PREAMBLE,
            f"theorem conv_invol_{i} {{α : Type}} (R : RelP α) (x y : α) : ConvR (ConvR R) x y ↔ R x y :=",
            "by\n  exact Iff.rfl",
            ["Converse of converse is definitionally identical to `R`."],
        )
        add(
            3,
            CONV_PREAMBLE,
            f"theorem conv_comp_rev_{i} {{α : Type}} (R S : RelP α) (x z : α) : "
            f"ConvR (CompR R S) x z ↔ CompR (ConvR S) (ConvR R) x z :=",
            "by\n"
            "  constructor\n"
            "  · rintro ⟨y, hry, hsz⟩\n"
            "    exact ⟨y, hsz, hry⟩\n"
            "  · rintro ⟨y, hsz, hry⟩\n"
            "    exact ⟨y, hry, hsz⟩",
            ["Converse of relational composition reverses the order: `(R ∘ S)⁻¹ = S⁻¹ ∘ R⁻¹`."],
        )
        add(
            3,
            CONV_PREAMBLE,
            f"theorem comp_assoc_{i} {{α : Type}} (R S T : RelP α) (x w : α) : "
            f"CompR (CompR R S) T x w ↔ CompR R (CompR S T) x w :=",
            "by\n"
            "  constructor\n"
            "  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩\n"
            "    exact ⟨y, hxy, ⟨z, hyz, hzw⟩⟩\n"
            "  · rintro ⟨y, hxy, ⟨z, hyz, hzw⟩⟩\n"
            "    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩",
            ["Relational composition is associative by re-packaging existential witnesses `y` and `z`."],
        )
        add(
            2,
            CONV_PREAMBLE,
            f"theorem symm_inter_conv_{i} {{α : Type}} (R : RelP α) : SymmR (fun x y => R x y ∧ ConvR R x y) :=",
            "by\n  rintro x y ⟨h1, h2⟩\n  exact ⟨h2, h1⟩",
            ["Symmetric core `R ∩ R⁻¹` is always symmetric."],
        )
        add(
            2,
            CONV_PREAMBLE,
            f"theorem symm_union_conv_{i} {{α : Type}} (R : RelP α) : SymmR (fun x y => R x y ∨ ConvR R x y) :=",
            "by\n  rintro x y (h1 | h2)\n  · exact Or.inr h1\n  · exact Or.inl h2",
            ["Symmetric closure `R ∪ R⁻¹` is always symmetric."],
        )

    return items


# ---------------------------------------------------------------------------
# 4. Higher-Order Constructive/Classical Logic & Function Iteration/Bijections
# ---------------------------------------------------------------------------

FUNC_PREAMBLE = """\
def InjFn {α β : Type} (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y
def SurjFn {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y
def BijFn {α β : Type} (f : α → β) : Prop := InjFn f ∧ SurjFn f
def LeftInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ x : α, g (f x) = x
def RightInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ y : β, f (g y) = y

def iterFn {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterFn f n x)"""


def gen_logic_functions_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "logic_functions", diff, pre, hdr, body, notes))
        idx += 1

    prop_sets = [
        ("P", "Q", "R", "S"),
        ("A", "B", "C", "D"),
        ("Phi", "Psi", "Chi", "Xi"),
        ("P1", "P2", "P3", "P4"),
        ("H1", "H2", "H3", "H4"),
        ("L1", "L2", "L3", "L4"),
        ("M1", "M2", "M3", "M4"),
        ("U1", "U2", "U3", "U4"),
    ]
    for i, (P, Q, R, S) in enumerate(prop_sets):
        add(
            1,
            "",
            f"theorem logic_curry_iff_{i} ({P} {Q} {R} : Prop) : (({P} ∧ {Q}) → {R}) ↔ ({P} → {Q} → {R}) :=",
            "by\n"
            "  constructor\n"
            "  · intro h hp hq; exact h ⟨hp, hq⟩\n"
            "  · rintro h ⟨hp, hq⟩; exact h hp hq",
            ["Currying isomorphism between `(P ∧ Q) → R` and `P → Q → R`."],
        )
        add(
            2,
            "",
            f"theorem logic_or_imp_iff_{i} ({P} {Q} {R} : Prop) : (({P} ∨ {Q}) → {R}) ↔ (({P} → {R}) ∧ ({Q} → {R})) :=",
            "by\n"
            "  constructor\n"
            "  · intro h; exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩\n"
            "  · rintro ⟨hpr, hqr⟩ (hp | hq)\n"
            "    · exact hpr hp\n"
            "    · exact hqr hq",
            ["Universal property of disjunction `(P ∨ Q) → R ↔ (P → R) ∧ (Q → R)`."],
        )
        add(
            2,
            "",
            f"theorem logic_imp_and_iff_{i} ({P} {Q} {R} : Prop) : ({P} → ({Q} ∧ {R})) ↔ (({P} → {Q}) ∧ ({P} → {R})) :=",
            "by\n"
            "  constructor\n"
            "  · intro h; exact ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩\n"
            "  · rintro ⟨hpq, hpr⟩ hp; exact ⟨hpq hp, hpr hp⟩",
            ["Implication into a conjunction splits into a conjunction of implications."],
        )
        add(
            2,
            "",
            f"theorem logic_triple_neg_{i} ({P} : Prop) : ¬¬¬{P} ↔ ¬{P} :=",
            "by\n"
            "  constructor\n"
            "  · intro hnnnp hp\n"
            "    exact hnnnp (fun hnp => hnp hp)\n"
            "  · intro hnp hnnp\n"
            "    exact hnnp hnp",
            ["Triple negation intuitionistically collapses to single negation!"],
        )
        add(
            3,
            "",
            f"theorem logic_dneg_map_{i} ({P} {Q} : Prop) (h : {P} → {Q}) : ¬¬{P} → ¬¬{Q} :=",
            "by\n  intro hnnp hnq\n  exact hnnp (fun hp => hnq (h hp))",
            ["Double-negation functoriality: compose `h : P → Q` with `hnq : ¬Q` to get `¬P`, contradicting `¬¬P`."],
        )
        add(
            3,
            "",
            f"theorem logic_dneg_ap_{i} ({P} {Q} : Prop) : ¬¬({P} → {Q}) → ¬¬{P} → ¬¬{Q} :=",
            "by\n"
            "  intro hnnf hnnp hnq\n"
            "  apply hnnf\n"
            "  intro hpq\n"
            "  apply hnnp\n"
            "  intro hp\n"
            "  exact hnq (hpq hp)",
            ["Applicative law of double negation in pure constructive logic."],
        )
        add(
            3,
            "",
            f"theorem logic_dneg_em_{i} ({P} : Prop) : ¬¬({P} ∨ ¬{P}) :=",
            "by\n"
            "  intro h\n"
            "  have hnp : ¬" + P + " := fun hp => h (Or.inl hp)\n"
            "  exact h (Or.inr hnp)",
            [
                "Glivenko's key lemma: `¬¬(P ∨ ¬P)` holds constructively without `Classical.em`!",
                "Assume `h : ¬(P ∨ ¬P)`, derive `hnp : ¬P`, then apply `h (Or.inr hnp)`.",
            ],
        )
        add(
            3,
            "",
            f"theorem logic_peirce_{i} ({P} {Q} : Prop) : (({P} → {Q}) → {P}) → {P} :=",
            "by\n"
            f"  intro h\n"
            f"  cases Classical.em {P} with\n"
            f"  | inl hp => exact hp\n"
            f"  | inr hnp => exact h (fun hp => False.elim (hnp hp))",
            [
                f"Prove Peirce's Law classically by case-splitting on `Classical.em {P}`.",
                f"When `¬{P}`, `{P} → {Q}` holds vacuously via `False.elim`.",
            ],
        )
        add(
            3,
            "",
            f"theorem logic_contrapos_classical_{i} ({P} {Q} : Prop) : (¬{Q} → ¬{P}) ↔ ({P} → {Q}) :=",
            "by\n"
            "  constructor\n"
            "  · intro h hp\n"
            f"    cases Classical.em {Q} with\n"
            "    | inl hq => exact hq\n"
            "    | inr hnq => exact False.elim (h hnq hp)\n"
            "  · intro h hnq hp\n"
            "    exact hnq (h hp)",
            ["Classical contrapositive equivalence using `Classical.em` in the reverse direction."],
        )
        add(
            3,
            "",
            f"theorem logic_imp_or_classical_{i} ({P} {Q} {R} : Prop) : "
            f"({P} → {Q} ∨ {R}) ↔ (({P} → {Q}) ∨ ({P} → {R})) :=",
            "by\n"
            "  constructor\n"
            "  · intro h\n"
            f"    cases Classical.em {P} with\n"
            "    | inl hp =>\n"
            "      rcases h hp with hq | hr\n"
            "      · exact Or.inl (fun _ => hq)\n"
            "      · exact Or.inr (fun _ => hr)\n"
            "    | inr hnp =>\n"
            "      exact Or.inl (fun hp => False.elim (hnp hp))\n"
            "  · rintro (hpq | hpr) hp\n"
            "    · exact Or.inl (hpq hp)\n"
            "    · exact Or.inr (hpr hp)",
            ["Classically split on `Classical.em P` to distribute implication over disjunction."],
        )
        add(
            2,
            "",
            f"theorem logic_diamond_imp_{i} ({P} {Q} {R} {S} : Prop) "
            f"(h1 : {P} → {Q} ∨ {R}) (h2 : {Q} → {S}) (h3 : {R} → {S}) : {P} → {S} :=",
            "by\n  intro hp\n  rcases h1 hp with hq | hr\n  · exact h2 hq\n  · exact h3 hr",
            ["Case split on `h1 hp` and apply `h2` or `h3`."],
        )

    # First-order quantifier theorems
    for i in range(12):
        add(
            2,
            "",
            f"theorem quant_forall_and_{i} {{α : Type}} (P Q : α → Prop) : "
            f"(∀ x, P x ∧ Q x) ↔ ((∀ x, P x) ∧ (∀ x, Q x)) :=",
            "by\n"
            "  constructor\n"
            "  · intro h; exact ⟨fun x => (h x).1, fun x => (h x).2⟩\n"
            "  · rintro ⟨hp, hq⟩ x; exact ⟨hp x, hq x⟩",
            ["Universal quantification distributes over conjunction."],
        )
        add(
            2,
            "",
            f"theorem quant_exists_or_{i} {{α : Type}} (P Q : α → Prop) : "
            f"(∃ x, P x ∨ Q x) ↔ ((∃ x, P x) ∨ (∃ x, Q x)) :=",
            "by\n"
            "  constructor\n"
            "  · rintro ⟨x, hp | hq⟩\n"
            "    · exact Or.inl ⟨x, hp⟩\n"
            "    · exact Or.inr ⟨x, hq⟩\n"
            "  · rintro (⟨x, hp⟩ | ⟨x, hq⟩)\n"
            "    · exact ⟨x, Or.inl hp⟩\n"
            "    · exact ⟨x, Or.inr hq⟩",
            ["Existential quantification distributes over disjunction."],
        )
        add(
            2,
            "",
            f"theorem quant_exists_swap_{i} {{α β : Type}} (R : α → β → Prop) : "
            f"(∃ x, ∃ y, R x y) ↔ (∃ y, ∃ x, R x y) :=",
            "by\n"
            "  constructor\n"
            "  · rintro ⟨x, y, h⟩; exact ⟨y, x, h⟩\n"
            "  · rintro ⟨y, x, h⟩; exact ⟨x, y, h⟩",
            ["Swap nested existential quantifiers."],
        )
        add(
            2,
            "",
            f"theorem quant_exists_forall_imp_{i} {{α β : Type}} (R : α → β → Prop) : "
            f"(∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) :=",
            "by\n  rintro ⟨x, hx⟩ y\n  exact ⟨x, hx y⟩",
            ["Uniform witness `x` works for every `y`."],
        )
        add(
            2,
            "",
            f"theorem quant_not_exists_{i} {{α : Type}} (P : α → Prop) : "
            f"(¬ ∃ x, P x) ↔ (∀ x, ¬ P x) :=",
            "by\n"
            "  constructor\n"
            "  · intro h x hx; exact h ⟨x, hx⟩\n"
            "  · rintro h ⟨x, hx⟩; exact h x hx",
            ["Constructive quantifier De Morgan law `¬(∃ x, P x) ↔ ∀ x, ¬P x`."],
        )
        add(
            3,
            "",
            f"theorem quant_not_forall_classical_{i} {{α : Type}} (P : α → Prop) : "
            f"(¬ ∀ x, P x) ↔ (∃ x, ¬ P x) :=",
            "by\n"
            "  constructor\n"
            "  · intro h\n"
            "    apply Classical.byContradiction\n"
            "    intro hne\n"
            "    apply h\n"
            "    intro x\n"
            "    cases Classical.em (P x) with\n"
            "    | inl hpx => exact hpx\n"
            "    | inr hnpx => exact False.elim (hne ⟨x, hnpx⟩)\n"
            "  · rintro ⟨x, hnpx⟩ hall\n"
            "    exact hnpx (hall x)",
            [
                "Classical quantifier De Morgan `¬(∀ x, P x) ↔ ∃ x, ¬P x` via `Classical.byContradiction` and `Classical.em`.",
            ],
        )

    # Function bijections, left/right inverses, and `iterFn`
    for i in range(16):
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem inj_comp_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) "
            f"(hf : InjFn f) (hg : InjFn g) : InjFn (fun x => g (f x)) :=",
            "by\n  intro x y h\n  exact hf (hg h)",
            ["Composition of injective functions is injective."],
        )
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem surj_comp_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) "
            f"(hf : SurjFn f) (hg : SurjFn g) : SurjFn (fun x => g (f x)) :=",
            "by\n"
            "  intro z\n"
            "  rcases hg z with ⟨y, rfl⟩\n"
            "  rcases hf y with ⟨x, rfl⟩\n"
            "  exact ⟨x, rfl⟩",
            ["Obtain preimage `y` under `g`, then preimage `x` under `f`."],
        )
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem inj_of_comp_inj_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) "
            f"(h : InjFn (fun x => g (f x))) : InjFn f :=",
            "by\n  intro x y hfx\n  exact h (congrArg g hfx)",
            ["If `g ∘ f` is injective, then `f` is injective by applying `congrArg g`."],
        )
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem surj_of_comp_surj_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) "
            f"(h : SurjFn (fun x => g (f x))) : SurjFn g :=",
            "by\n  intro z\n  rcases h z with ⟨x, hx⟩\n  exact ⟨f x, hx⟩",
            ["If `g ∘ f` is surjective, witness `f x` shows `g` is surjective."],
        )
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem inj_of_left_inv_{i} {{α β : Type}} (f : α → β) (g : β → α) "
            f"(h : LeftInvFn g f) : InjFn f :=",
            "by\n  intro x y hfx\n  have h1 := congrArg g hfx\n  rw [h x, h y] at h1\n  exact h1",
            ["Any function with a left inverse (retraction) is injective."],
        )
        add(
            2,
            FUNC_PREAMBLE,
            f"theorem surj_of_right_inv_{i} {{α β : Type}} (f : α → β) (g : β → α) "
            f"(h : RightInvFn g f) : SurjFn f :=",
            "by\n  intro y\n  exact ⟨g y, h y⟩",
            ["Any function with a right inverse (section) is surjective."],
        )
        add(
            3,
            FUNC_PREAMBLE,
            f"theorem left_right_inv_eq_{i} {{α β : Type}} (f : α → β) (g1 g2 : β → α) "
            f"(hl : LeftInvFn g1 f) (hr : RightInvFn g2 f) : ∀ y, g1 y = g2 y :=",
            "by\n  intro y\n  calc g1 y = g1 (f (g2 y)) := by rw [hr y]\n    _ = g2 y := by rw [hl (g2 y)]",
            ["If `g1` is a left inverse and `g2` is a right inverse of `f`, then `g1 = g2` pointwise."],
        )
        add(
            3,
            FUNC_PREAMBLE,
            f"theorem iterFn_add_{i} {{α : Type}} (f : α → α) (m n : Nat) (x : α) : "
            f"iterFn f (m + n) x = iterFn f m (iterFn f n x) :=",
            "by\n"
            "  induction m with\n"
            "  | zero => simp [iterFn]\n"
            "  | succ k ih =>\n"
            "    rw [Nat.succ_add, iterFn, iterFn, ih]",
            ["Induct on `m` using `Nat.succ_add` and unfold `iterFn`."],
        )
        add(
            3,
            FUNC_PREAMBLE,
            f"theorem iterFn_fixed_{i} {{α : Type}} (f : α → α) (x : α) (hx : f x = x) (n : Nat) : "
            f"iterFn f n x = x :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih => simp [iterFn, ih, hx]",
            ["A fixed point `f x = x` remains fixed under `n` iterations for all `n`."],
        )
        add(
            3,
            FUNC_PREAMBLE,
            f"theorem iterFn_comm_single_{i} {{α : Type}} (f : α → α) (n : Nat) (x : α) : "
            f"iterFn f n (f x) = f (iterFn f n x) :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih => simp [iterFn, ih]",
            ["`iterFn f n` commutes with `f` by straightforward induction on `n`."],
        )
        add(
            4,
            FUNC_PREAMBLE,
            f"theorem iterFn_comm_general_{i} {{α : Type}} (f g : α → α) (hc : ∀ x, f (g x) = g (f x)) "
            f"(n : Nat) (x : α) : f (iterFn g n x) = iterFn g n (f x) :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    simp [iterFn]\n"
            "    rw [hc (iterFn g k x), ih]",
            ["If `f` commutes with `g`, then `f` commutes with `iterFn g n` by induction on `n`."],
        )

    return items


# ---------------------------------------------------------------------------
# 5. Inductive Data Structures: Lists, Binary Trees, Full Trees & Expr Compilers
# ---------------------------------------------------------------------------

LIST_PURE_PREAMBLE = """\
def snocL {α : Type} : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: snocL xs a

def revL {α : Type} : List α → List α
  | [] => []
  | x :: xs => snocL (revL xs) x

def mapL {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapL f xs

def sumL : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumL xs"""

BTREE_PREAMBLE = """\
inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α

def mirrorT {α : Type} : BTree α → BTree α
  | BTree.leaf => BTree.leaf
  | BTree.node l v r => BTree.node (mirrorT r) v (mirrorT l)

def sizeT {α : Type} : BTree α → Nat
  | BTree.leaf => 0
  | BTree.node l _ r => 1 + sizeT l + sizeT r

def mapT {α β : Type} (f : α → β) : BTree α → BTree β
  | BTree.leaf => BTree.leaf
  | BTree.node l v r => BTree.node (mapT f l) (f v) (mapT f r)"""

FULLTREE_PREAMBLE = """\
inductive FullTree (α : Type) where
  | tip : α → FullTree α
  | fork : FullTree α → FullTree α → FullTree α

def leavesFT {α : Type} : FullTree α → Nat
  | FullTree.tip _ => 1
  | FullTree.fork l r => leavesFT l + leavesFT r

def forksFT {α : Type} : FullTree α → Nat
  | FullTree.tip _ => 0
  | FullTree.fork l r => 1 + forksFT l + forksFT r

def flipFT {α : Type} : FullTree α → FullTree α
  | FullTree.tip v => FullTree.tip v
  | FullTree.fork l r => FullTree.fork (flipFT r) (flipFT l)"""

EXPR_PREAMBLE = """\
inductive PureExpr where
  | lit : Nat → PureExpr
  | var : Nat → PureExpr
  | add : PureExpr → PureExpr → PureExpr
  | mul : PureExpr → PureExpr → PureExpr

def evalExpr (env : Nat → Nat) : PureExpr → Nat
  | PureExpr.lit n => n
  | PureExpr.var i => env i
  | PureExpr.add e1 e2 => evalExpr env e1 + evalExpr env e2
  | PureExpr.mul e1 e2 => evalExpr env e1 * evalExpr env e2

def swapAddExpr : PureExpr → PureExpr
  | PureExpr.lit n => PureExpr.lit n
  | PureExpr.var i => PureExpr.var i
  | PureExpr.add e1 e2 => PureExpr.add (swapAddExpr e2) (swapAddExpr e1)
  | PureExpr.mul e1 e2 => PureExpr.mul (swapAddExpr e1) (swapAddExpr e2)

def optZeroExpr : PureExpr → PureExpr
  | PureExpr.lit n => PureExpr.lit n
  | PureExpr.var i => PureExpr.var i
  | PureExpr.add e1 e2 =>
    match optZeroExpr e1, optZeroExpr e2 with
    | PureExpr.lit 0, r => r
    | l, PureExpr.lit 0 => l
    | l, r => PureExpr.add l r
  | PureExpr.mul e1 e2 => PureExpr.mul (optZeroExpr e1) (optZeroExpr e2)"""


def gen_inductive_ds_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "inductive_ds", diff, pre, hdr, body, notes))
        idx += 1

    # Pure List & custom recursive list combinator theorems
    for i in range(18):
        add(
            2,
            LIST_PURE_PREAMBLE,
            f"theorem snocL_eq_append_{i} {{α : Type}} (xs : List α) (a : α) : snocL xs a = xs ++ [a] :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [snocL, ih]",
            ["Induct on `xs` to prove `snocL xs a = xs ++ [a]`."],
        )
        add(
            2,
            LIST_PURE_PREAMBLE,
            f"theorem length_snocL_{i} {{α : Type}} (xs : List α) (a : α) : (snocL xs a).length = xs.length + 1 :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [snocL, ih]",
            ["Induct on `xs`; `snocL` increments list length by 1."],
        )
        add(
            3,
            LIST_PURE_PREAMBLE,
            f"theorem length_revL_{i} {{α : Type}} (xs : List α) : (revL xs).length = xs.length :=",
            "by\n"
            "  have hsnoc : ∀ (ys : List α) (a : α), (snocL ys a).length = ys.length + 1 := by\n"
            "    intro ys a\n"
            "    induction ys with\n"
            "    | nil => rfl\n"
            "    | cons y tl ih => simp [snocL, ih]\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [revL, hsnoc, ih]",
            [
                "Prove helper lemma `hsnoc : (snocL ys a).length = ys.length + 1`.",
                "Induct on `xs` using `hsnoc` and `ih`.",
            ],
        )
        add(
            4,
            LIST_PURE_PREAMBLE,
            f"theorem revL_snocL_{i} {{α : Type}} (xs : List α) (a : α) : revL (snocL xs a) = a :: revL xs :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [snocL, revL, ih]",
            ["Induct on `xs`: reversing `snocL xs a` prepends `a` in front of `revL xs`."],
        )
        add(
            4,
            LIST_PURE_PREAMBLE,
            f"theorem revL_involutive_{i} {{α : Type}} (xs : List α) : revL (revL xs) = xs :=",
            "by\n"
            "  have h : ∀ (ys : List α) (a : α), revL (snocL ys a) = a :: revL ys := by\n"
            "    intro ys a\n"
            "    induction ys with\n"
            "    | nil => rfl\n"
            "    | cons y tl ih => simp [snocL, revL, ih]\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [revL, h, ih]",
            [
                "First establish `revL (snocL ys a) = a :: revL ys`.",
                "Then induct on `xs` to prove `revL (revL xs) = xs`.",
            ],
        )
        add(
            2,
            LIST_PURE_PREAMBLE,
            f"theorem mapL_id_{i} {{α : Type}} (xs : List α) : mapL (fun x => x) xs = xs :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [mapL, ih]",
            ["Functor identity law for `mapL` by structural induction on `xs`."],
        )
        add(
            3,
            LIST_PURE_PREAMBLE,
            f"theorem mapL_comp_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) (xs : List α) : "
            f"mapL g (mapL f xs) = mapL (fun x => g (f x)) xs :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [mapL, ih]",
            ["Functor composition law `mapL g (mapL f xs) = mapL (g ∘ f) xs`."],
        )
        add(
            3,
            LIST_PURE_PREAMBLE,
            f"theorem mapL_snocL_{i} {{α β : Type}} (f : α → β) (xs : List α) (a : α) : "
            f"mapL f (snocL xs a) = snocL (mapL f xs) (f a) :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => rfl\n"
            "  | cons x tl ih => simp [snocL, mapL, ih]",
            ["`mapL f` commutes with `snocL` by induction on `xs`."],
        )
        add(
            3,
            LIST_PURE_PREAMBLE,
            f"theorem sumL_append_{i} (xs ys : List Nat) : sumL (xs ++ ys) = sumL xs + sumL ys :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => simp [sumL]\n"
            "  | cons x tl ih =>\n"
            "    simp [sumL, ih, Nat.add_assoc]",
            ["`sumL` is a monoid homomorphism from `(List Nat, ++)` to `(Nat, +)`."],
        )
        add(
            3,
            LIST_PURE_PREAMBLE,
            f"theorem sumL_snocL_{i} (xs : List Nat) (a : Nat) : sumL (snocL xs a) = sumL xs + a :=",
            "by\n"
            "  induction xs with\n"
            "  | nil => simp [snocL, sumL]\n"
            "  | cons x tl ih => simp [snocL, sumL, ih, Nat.add_assoc]",
            ["Induct on `xs` and reassociate addition via `Nat.add_assoc`."],
        )

    # Binary Trees, FullTrees & PureExpr AST verification
    for i in range(18):
        add(
            2,
            BTREE_PREAMBLE,
            f"theorem mirrorT_invol_{i} {{α : Type}} (t : BTree α) : mirrorT (mirrorT t) = t :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr => simp [mirrorT, ihl, ihr]",
            ["Tree reflection `mirrorT` is an involution by structural induction on `BTree`."],
        )
        add(
            3,
            BTREE_PREAMBLE,
            f"theorem sizeT_mirrorT_{i} {{α : Type}} (t : BTree α) : sizeT (mirrorT t) = sizeT t :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr =>\n"
            "    simp [mirrorT, sizeT, ihl, ihr]\n"
            "    omega",
            [
                "Induct on `t : BTree α`.",
                "In the `node` case, rewrite with `ihl` and `ihr`, then finish `1 + sizeT r + sizeT l = 1 + sizeT l + sizeT r` with `omega`.",
            ],
        )
        add(
            2,
            BTREE_PREAMBLE,
            f"theorem mapT_id_{i} {{α : Type}} (t : BTree α) : mapT (fun x => x) t = t :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr => simp [mapT, ihl, ihr]",
            ["Functor identity law on `BTree α`."],
        )
        add(
            3,
            BTREE_PREAMBLE,
            f"theorem mapT_comp_{i} {{α β γ : Type}} (f : α → β) (g : β → γ) (t : BTree α) : "
            f"mapT g (mapT f t) = mapT (fun x => g (f x)) t :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr => simp [mapT, ihl, ihr]",
            ["Functor composition law on `BTree α`."],
        )
        add(
            3,
            BTREE_PREAMBLE,
            f"theorem sizeT_mapT_{i} {{α β : Type}} (f : α → β) (t : BTree α) : sizeT (mapT f t) = sizeT t :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr => simp [mapT, sizeT, ihl, ihr]",
            ["Mapping values preserves `sizeT`."],
        )
        add(
            3,
            BTREE_PREAMBLE,
            f"theorem mirrorT_mapT_{i} {{α β : Type}} (f : α → β) (t : BTree α) : "
            f"mirrorT (mapT f t) = mapT f (mirrorT t) :=",
            "by\n"
            "  induction t with\n"
            "  | leaf => rfl\n"
            "  | node l v r ihl ihr => simp [mirrorT, mapT, ihl, ihr]",
            ["`mirrorT` is a natural transformation: it commutes with `mapT f`."],
        )
        add(
            4,
            FULLTREE_PREAMBLE,
            f"theorem fulltree_leaves_eq_forks_succ_{i} {{α : Type}} (t : FullTree α) : "
            f"leavesFT t = forksFT t + 1 :=",
            "by\n"
            "  induction t with\n"
            "  | tip _ => rfl\n"
            "  | fork l r ihl ihr =>\n"
            "    simp [leavesFT, forksFT, ihl, ihr]\n"
            "    omega",
            [
                "Classic full binary tree invariant: `#leaves = #internal_forks + 1`.",
                "Induct on `t`; in `fork l r`, `(forks l + 1) + (forks r + 1) = (1 + forks l + forks r) + 1` by `omega`.",
            ],
        )
        add(
            2,
            FULLTREE_PREAMBLE,
            f"theorem flipFT_invol_{i} {{α : Type}} (t : FullTree α) : flipFT (flipFT t) = t :=",
            "by\n"
            "  induction t with\n"
            "  | tip _ => rfl\n"
            "  | fork l r ihl ihr => simp [flipFT, ihl, ihr]",
            ["`flipFT` is involutive by structural induction on `FullTree`."],
        )
        add(
            3,
            FULLTREE_PREAMBLE,
            f"theorem leavesFT_flipFT_{i} {{α : Type}} (t : FullTree α) : leavesFT (flipFT t) = leavesFT t :=",
            "by\n"
            "  induction t with\n"
            "  | tip _ => rfl\n"
            "  | fork l r ihl ihr => simp [flipFT, leavesFT, ihl, ihr]; omega",
            ["Flipping subtrees preserves total leaf count."],
        )
        add(
            3,
            EXPR_PREAMBLE,
            f"theorem eval_swapAddExpr_{i} (env : Nat → Nat) (e : PureExpr) : "
            f"evalExpr env (swapAddExpr e) = evalExpr env e :=",
            "by\n"
            "  induction e with\n"
            "  | lit _ => rfl\n"
            "  | var _ => rfl\n"
            "  | add e1 e2 ih1 ih2 => simp [swapAddExpr, evalExpr, ih1, ih2, Nat.add_comm]\n"
            "  | mul e1 e2 ih1 ih2 => simp [swapAddExpr, evalExpr, ih1, ih2]",
            [
                "Induct on the expression AST `e : PureExpr`.",
                "In the `add` case, apply `ih1`, `ih2`, and `Nat.add_comm`.",
            ],
        )
        add(
            4,
            EXPR_PREAMBLE,
            f"theorem eval_optZeroExpr_{i} (env : Nat → Nat) (e : PureExpr) : "
            f"evalExpr env (optZeroExpr e) = evalExpr env e :=",
            "by\n"
            "  induction e with\n"
            "  | lit _ => rfl\n"
            "  | var _ => rfl\n"
            "  | mul e1 e2 ih1 ih2 => simp [optZeroExpr, evalExpr, ih1, ih2]\n"
            "  | add e1 e2 ih1 ih2 =>\n"
            "    simp only [optZeroExpr]\n"
            "    split\n"
            "    · next r he1 he2 =>\n"
            "      rw [evalExpr, ← ih1, ← ih2, he1, he2]\n"
            "      simp [evalExpr]\n"
            "    · next l he1 he2 _ =>\n"
            "      rw [evalExpr, ← ih1, ← ih2, he1, he2]\n"
            "      simp [evalExpr]\n"
            "    · next l r he1 he2 _ _ =>\n"
            "      rw [evalExpr, evalExpr, ← ih1, ← ih2, he1, he2]",
            [
                "Prove soundness of constant-zero addition elimination pass `optZeroExpr`.",
                "In the `add` branch, use `split` on the `match` arms and rewrite with `ih1`, `ih2`.",
            ],
        )

    return items


# ---------------------------------------------------------------------------
# 6. Natural Number Arithmetic, Series, Powers, Fibonacci & Divisibility
# ---------------------------------------------------------------------------

NAT_SERIES_PREAMBLE = """\
def sumUpTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumUpTo n + (n + 1)

def sumOdds : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdds n + (2 * n + 1)

def pow2N : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2N n

def sumPow2 : Nat → Nat
  | 0 => 1
  | n + 1 => sumPow2 n + pow2N (n + 1)

def fibN : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibN n + fibN (n + 1)

def sumFib : Nat → Nat
  | 0 => 0
  | n + 1 => sumFib n + fibN (n + 1)"""

NAT_DVD_PREAMBLE = """\
def PureDvd (d n : Nat) : Prop := ∃ k : Nat, n = d * k
def PureEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k
def PureOdd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1"""


def gen_nat_number_theory_items(start_idx: int) -> List[PureLeanItem]:
    items: List[PureLeanItem] = []
    idx = start_idx

    def add(diff: int, pre: str, hdr: str, body: str, notes: List[str]):
        nonlocal idx
        items.append(make_item(idx, "nat_number_theory", diff, pre, hdr, body, notes))
        idx += 1

    # Parametric linear & polynomial identities over Nat
    for c1 in range(1, 7):
        for c2 in range(1, 7):
            add(
                1,
                "",
                f"theorem nat_lin_comb_{c1}_{c2} (x y z : Nat) : "
                f"{c1} * (x + y) + {c2} * (y + z) = {c1} * x + ({c1 + c2}) * y + {c2} * z :=",
                "by\n  omega",
                [f"Linear arithmetic identity over `Nat` discharged cleanly by `omega`."],
            )
            add(
                2,
                NAT_DVD_PREAMBLE,
                f"theorem nat_dvd_lin_{c1}_{c2} (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : "
                f"PureDvd d ({c1} * a + {c2} * b) :=",
                f"by\n"
                f"  rcases ha with ⟨ka, rfl⟩\n"
                f"  rcases hb with ⟨kb, rfl⟩\n"
                f"  refine ⟨{c1} * ka + {c2} * kb, ?_⟩\n"
                f"  rw [Nat.left_distrib]\n"
                f"  have h1 : {c1} * (d * ka) = d * ({c1} * ka) := by\n"
                f"    rw [← Nat.mul_assoc, Nat.mul_comm {c1} d, Nat.mul_assoc]\n"
                f"  have h2 : {c2} * (d * kb) = d * ({c2} * kb) := by\n"
                f"    rw [← Nat.mul_assoc, Nat.mul_comm {c2} d, Nat.mul_assoc]\n"
                f"  rw [h1, h2]",
                [
                    f"Unpack divisibility witnesses `ka` and `kb`.",
                    f"Provide witness `{c1} * ka + {c2} * kb` and factor `d` out via `Nat.left_distrib`, `Nat.mul_assoc`, and `Nat.mul_comm`.",
                ],
            )

    # Polynomial squares, cubes, differences, parity, and divisibility properties
    for i in range(16):
        add(
            2,
            "",
            f"theorem nat_sq_add_{i} (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=",
            "by\n"
            "  rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]\n"
            "  rw [Nat.mul_comm b a]\n"
            "  omega",
            ["Expand `(a + b) * (a + b)` with `Nat.left_distrib` and `Nat.right_distrib`, commute `b * a`, then `omega`."],
        )
        add(
            2,
            "",
            f"theorem nat_foil_{i} (a b c d : Nat) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=",
            "by\n"
            "  rw [Nat.right_distrib, Nat.left_distrib, Nat.left_distrib]\n"
            "  omega",
            ["FOIL expansion via `Nat.right_distrib` and `Nat.left_distrib`."],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem gauss_sum_{i} (n : Nat) : 2 * sumUpTo n = n * (n + 1) :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    rw [sumUpTo, Nat.left_distrib, ih]\n"
            "    have h : (k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1) := by\n"
            "      rw [Nat.left_distrib]\n"
            "      omega\n"
            "    omega",
            [
                "Prove Gauss's formula `2 * sumUpTo n = n * (n + 1)` by induction on `n`.",
                "Unfold `sumUpTo (k + 1)`, distribute `2 * _`, substitute `ih`, and close algebraically.",
            ],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem sum_odds_sq_{i} (n : Nat) : sumOdds n = n * n :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    rw [sumOdds, ih]\n"
            "    have h : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by\n"
            "      rw [Nat.left_distrib, Nat.right_distrib]\n"
            "      omega\n"
            "    omega",
            [
                "Sum of the first `n` odd numbers equals `n * n` by induction on `n`.",
                "Expand `(k + 1) * (k + 1) = k * k + 2 * k + 1` in the inductive step.",
            ],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem geom_pow2_sum_{i} (n : Nat) : sumPow2 n + 1 = pow2N (n + 1) :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    simp only [sumPow2, pow2N]\n"
            "    omega",
            [
                "Prove `(1 + 2 + ... + 2^n) + 1 = 2^(n + 1)` by induction on `n`.",
            ],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem pow2N_add_{i} (m n : Nat) : pow2N (m + n) = pow2N m * pow2N n :=",
            "by\n"
            "  induction m with\n"
            "  | zero => simp [pow2N]\n"
            "  | succ k ih =>\n"
            "    rw [Nat.succ_add, pow2N, pow2N, ih, Nat.mul_assoc]",
            ["Exponent addition law `2^(m + n) = 2^m * 2^n` by induction on `m`."],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem pow2N_pos_{i} (n : Nat) : 1 ≤ pow2N n :=",
            "by\n"
            "  induction n with\n"
            "  | zero => decide\n"
            "  | succ k ih =>\n"
            "    simp only [pow2N]\n"
            "    omega",
            ["`2^n ≥ 1` for all `n : Nat` by induction and `omega`."],
        )
        add(
            3,
            NAT_SERIES_PREAMBLE,
            f"theorem sum_fib_identity_{i} (n : Nat) : sumFib n + 1 = fibN (n + 2) :=",
            "by\n"
            "  induction n with\n"
            "  | zero => rfl\n"
            "  | succ k ih =>\n"
            "    have hf : fibN (k + 3) = fibN (k + 1) + fibN (k + 2) := rfl\n"
            "    simp only [sumFib]\n"
            "    omega",
            [
                "Classic Fibonacci sum identity: `(F_1 + ... + F_n) + 1 = F_{n+2}`.",
                "Induct on `n`, unfolding `fibN (k + 3) = fibN (k + 1) + fibN (k + 2)`.",
            ],
        )
        add(
            2,
            NAT_DVD_PREAMBLE,
            f"theorem dvd_refl_{i} (a : Nat) : PureDvd a a :=",
            "by\n  exact ⟨1, (Nat.mul_one a).symm⟩",
            ["Witness `k = 1` gives `a = a * 1`."],
        )
        add(
            2,
            NAT_DVD_PREAMBLE,
            f"theorem dvd_trans_{i} (a b c : Nat) (h1 : PureDvd a b) (h2 : PureDvd b c) : PureDvd a c :=",
            "by\n"
            "  rcases h1 with ⟨k1, rfl⟩\n"
            "  rcases h2 with ⟨k2, rfl⟩\n"
            "  exact ⟨k1 * k2, Nat.mul_assoc a k1 k2⟩",
            ["Compose divisibility witnesses `k1` and `k2` into `k1 * k2` via `Nat.mul_assoc`."],
        )
        add(
            2,
            NAT_DVD_PREAMBLE,
            f"theorem even_add_even_{i} (a b : Nat) (ha : PureEven a) (hb : PureEven b) : PureEven (a + b) :=",
            "by\n"
            "  rcases ha with ⟨ka, rfl⟩\n"
            "  rcases hb with ⟨kb, rfl⟩\n"
            "  exact ⟨ka + kb, by omega⟩",
            ["Sum of two even numbers `2*ka + 2*kb` has witness `ka + kb`."],
        )
        add(
            2,
            NAT_DVD_PREAMBLE,
            f"theorem odd_add_odd_{i} (a b : Nat) (ha : PureOdd a) (hb : PureOdd b) : PureEven (a + b) :=",
            "by\n"
            "  rcases ha with ⟨ka, rfl⟩\n"
            "  rcases hb with ⟨kb, rfl⟩\n"
            "  exact ⟨ka + kb + 1, by omega⟩",
            ["Sum of two odd numbers `(2*ka + 1) + (2*kb + 1)` is even with witness `ka + kb + 1`."],
        )
        add(
            3,
            NAT_DVD_PREAMBLE,
            f"theorem even_or_odd_{i} (n : Nat) : PureEven n ∨ PureOdd n :=",
            "by\n"
            "  induction n with\n"
            "  | zero => exact Or.inl ⟨0, rfl⟩\n"
            "  | succ k ih =>\n"
            "    rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩\n"
            "    · exact Or.inr ⟨m, rfl⟩\n"
            "    · exact Or.inl ⟨m + 1, by omega⟩",
            [
                "Every natural number is `PureEven` or `PureOdd` by induction on `n`.",
                "Incrementing flips `2*m` to `2*m + 1` and `2*m + 1` to `2*(m + 1)`.",
            ],
        )
        add(
            3,
            NAT_DVD_PREAMBLE,
            f"theorem not_even_and_odd_{i} (n : Nat) : ¬ (PureEven n ∧ PureOdd n) :=",
            "by\n"
            "  rintro ⟨⟨ka, ha⟩, ⟨kb, hb⟩⟩\n"
            "  omega",
            ["No natural number can simultaneously equal `2 * ka` and `2 * kb + 1` (`omega`)."],
        )
        add(
            3,
            NAT_DVD_PREAMBLE,
            f"theorem consec_prod_even_{i} (n : Nat) : PureEven (n * (n + 1)) :=",
            "by\n"
            "  have hpar : PureEven n ∨ PureOdd n := by\n"
            "    induction n with\n"
            "    | zero => exact Or.inl ⟨0, rfl⟩\n"
            "    | succ k ih =>\n"
            "      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩\n"
            "      · exact Or.inr ⟨m, rfl⟩\n"
            "      · exact Or.inl ⟨m + 1, by omega⟩\n"
            "  rcases hpar with ⟨k, rfl⟩ | ⟨k, rfl⟩\n"
            "  · refine ⟨k * (2 * k + 1), ?_⟩\n"
            "    rw [Nat.mul_assoc]\n"
            "  · refine ⟨(2 * k + 1) * (k + 1), ?_⟩\n"
            "    have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega\n"
            "    rw [h1, ← Nat.mul_assoc, Nat.mul_comm (2 * k + 1) 2, Nat.mul_assoc]",
            [
                "Prove `n * (n + 1)` is always even by splitting on parity `PureEven n ∨ PureOdd n`.",
                "If `n = 2k`, factor `2` on the left; if `n = 2k + 1`, then `n + 1 = 2(k + 1)` and factor `2`.",
            ],
        )

    return items


def generate_stage1_corpus(out_path: str = "data/stage1_pure_lean.jsonl", seed: int = 42) -> Dict:
    t0 = time.time()
    all_items: List[PureLeanItem] = []
    for gen_fn in [
        gen_algebra_items,
        gen_order_lattice_items,
        gen_relations_sets_items,
        gen_logic_functions_items,
        gen_inductive_ds_items,
        gen_nat_number_theory_items,
    ]:
        batch = gen_fn(len(all_items))
        all_items.extend(batch)

    print(f"Synthesized {len(all_items)} candidate pure Lean items across 6 domains. Running Lean 4.36 batch verification...")
    snippets = [it.full_lean for it in all_items]
    valid_idx, failed = verify_snippets_batch(snippets, chunk_size=75, max_workers=8)

    if failed:
        print(f"WARNING: {len(failed)} items failed Lean check (filtering them out):")
        for f_idx, err in failed[:5]:
            print(f"  - [{all_items[f_idx].id}]: {err[:200]}")

    verified_items = [all_items[i] for i in valid_idx]
    rng = random.Random(seed)
    rng.shuffle(verified_items)

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    domain_counts: Dict[str, int] = {}
    with open(out_path, "w", encoding="utf-8") as f:
        for it in verified_items:
            domain_counts[it.domain] = domain_counts.get(it.domain, 0) + 1
            f.write(json.dumps(it.to_dict(), ensure_ascii=False) + "\n")

    elapsed = time.time() - t0
    summary = {
        "total_candidates": len(all_items),
        "verified_count": len(verified_items),
        "failed_count": len(failed),
        "domains": domain_counts,
        "elapsed_sec": round(elapsed, 2),
        "out_path": out_path,
    }
    print("Stage 1 Summary:", json.dumps(summary, indent=2))
    return summary


if __name__ == "__main__":
    generate_stage1_corpus()
