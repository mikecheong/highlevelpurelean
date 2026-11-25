"""
Stage 3 Hard Pure Lean 4 Question Bank (15 multi-step theorems for per-question GRPO)
+ 12 Held-Out Unseen Pure Lean Evaluation Theorems.
Every single reference solution is formally verified with `verify_single_proof`
(including `#print axioms` kernel verification in Lean 4.36).
"""

from __future__ import annotations

import json
import os
from typing import Dict, List

from src.lean_verifier import verify_single_proof
from src.prompts import build_assistant_sketchpad_response


def build_hard_grpo_questions() -> List[Dict]:
    return [
        # 1. Abstract Algebra: Groups of exponent 2 are abelian
        {
            "id": "hq_01_exp2_group_comm",
            "domain": "algebra",
            "title": "Groups of Exponent 2 Are Abelian",
            "preamble": (
                "class PureGroup (G : Type) where\n"
                "  mul : G → G → G\n"
                "  one : G\n"
                "  inv : G → G\n"
                "  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)\n"
                "  one_mul : ∀ a : G, mul one a = a\n"
                "  mul_one : ∀ a : G, mul a one = a\n"
                "  inv_mul : ∀ a : G, mul (inv a) a = one\n"
                "  mul_inv : ∀ a : G, mul a (inv a) = one"
            ),
            "theorem_header": (
                "theorem exp2_group_abelian {G : Type} [PureGroup G] "
                "(hexp : ∀ x : G, PureGroup.mul x x = PureGroup.one) (a b : G) : "
                "PureGroup.mul a b = PureGroup.mul b a :="
            ),
            "warmup_hint": (
                "First prove `hself : ∀ x : G, x = PureGroup.inv x` by left-multiplying `hexp x` by `inv x`, "
                "or compute `mul (mul a b) (mul b a) = one` using `hexp b` and `hexp a` and compare with `hexp (mul a b)`."
            ),
            "reference_sketchpad": (
                "In a group where `x * x = 1` for all `x`, we want `a * b = b * a`.\n"
                "Observe `(a * b) * (a * b) = 1` by `hexp (mul a b)`, and also `(a * b) * (b * a) = a * (b * b) * a = a * 1 * a = a * a = 1`!\n"
                "Therefore `(a * b) * (a * b) = (a * b) * (b * a)`.\n"
                "Left-multiplying both sides by `inv (mul a b)` cancels `a * b` and yields `a * b = b * a`!"
            ),
            "reference_proof": (
                "by\n"
                "  have h1 : PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a) = PureGroup.one := by\n"
                "    calc PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a)\n"
                "      _ = PureGroup.mul a (PureGroup.mul b (PureGroup.mul b a)) := by rw [PureGroup.mul_assoc]\n"
                "      _ = PureGroup.mul a (PureGroup.mul (PureGroup.mul b b) a) := by rw [← PureGroup.mul_assoc b b a]\n"
                "      _ = PureGroup.one := by rw [hexp b, PureGroup.one_mul, hexp a]\n"
                "  have h2 : PureGroup.mul (PureGroup.mul a b) (PureGroup.mul a b) = "
                "PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a) := by\n"
                "    rw [hexp (PureGroup.mul a b), h1]\n"
                "  calc PureGroup.mul a b\n"
                "    _ = PureGroup.mul PureGroup.one (PureGroup.mul a b) := by rw [PureGroup.one_mul]\n"
                "    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul a b)) (PureGroup.mul a b) := by rw [PureGroup.inv_mul]\n"
                "    _ = PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul (PureGroup.mul a b) (PureGroup.mul a b)) := by rw [PureGroup.mul_assoc]\n"
                "    _ = PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a)) := by rw [h2]\n"
                "    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul a b)) (PureGroup.mul b a) := by rw [← PureGroup.mul_assoc]\n"
                "    _ = PureGroup.mul b a := by rw [PureGroup.inv_mul, PureGroup.one_mul]"
            ),
        },
        # 2. Order & Galois Connections: Dual stabilization u (l (u b)) = u b
        {
            "id": "hq_02_galois_u_l_u",
            "domain": "order_lattice",
            "title": "Upper Adjoint Stabilization u(l(u(b))) = u(b)",
            "preamble": (
                "class PurePoset (P : Type) where\n"
                "  le : P → P → Prop\n"
                "  le_refl : ∀ a : P, le a a\n"
                "  le_trans : ∀ {a b c : P}, le a b → le b c → le a c\n"
                "  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b\n\n"
                "structure GaloisConn (A B : Type) [PurePoset A] [PurePoset B] (l : A → B) (u : B → A) : Prop where\n"
                "  adj : ∀ a b, PurePoset.le (l a) b ↔ PurePoset.le a (u b)"
            ),
            "theorem_header": (
                "theorem galois_u_l_u {A B : Type} [PurePoset A] [PurePoset B] "
                "(l : A → B) (u : B → A) (hgc : GaloisConn A B l u) (b : B) : "
                "u (l (u b)) = u b :="
            ),
            "warmup_hint": (
                "Apply `PurePoset.le_antisymm`. For `u (l (u b)) ≤ u b`, transpose across `hgc.adj` at `(u (l (u b)), b)` "
                "using counit `l (u _) ≤ _` twice. For `u b ≤ u (l (u b))`, use unit at `a = u b`."
            ),
            "reference_sketchpad": (
                "We prove `u (l (u b)) = u b` via `PurePoset.le_antisymm`.\n"
                "1. Direction `u (l (u b)) ≤ u b`: by `(hgc.adj (u (l (u b))) b).mp`, it suffices to show `l (u (l (u b))) ≤ b`.\n"
                "   Counit at `l (u b)` gives `l (u (l (u b))) ≤ l (u b)`, and counit at `b` gives `l (u b) ≤ b`; chain with `le_trans`!\n"
                "2. Direction `u b ≤ u (l (u b))`: this is directly the unit `(hgc.adj (u b) (l (u b))).mp (le_refl _)`!"
            ),
            "reference_proof": (
                "by\n"
                "  apply PurePoset.le_antisymm\n"
                "  · have hc1 : PurePoset.le (l (u (l (u b)))) (l (u b)) := "
                "(hgc.adj (u (l (u b))) (l (u b))).mpr (PurePoset.le_refl _)\n"
                "    have hc2 : PurePoset.le (l (u b)) b := (hgc.adj (u b) b).mpr (PurePoset.le_refl _)\n"
                "    exact (hgc.adj (u (l (u b))) b).mp (PurePoset.le_trans hc1 hc2)\n"
                "  · exact (hgc.adj (u b) (l (u b))).mp (PurePoset.le_refl _)"
            ),
        },
        # 3. Classical First-Order Logic: Constant Domain / Reverse Or-Forall Law
        {
            "id": "hq_03_classical_forall_or",
            "domain": "logic_functions",
            "title": "Classical Quantifier Distribution (∀ x, P ∨ Q x) → P ∨ (∀ x, Q x)",
            "preamble": "",
            "theorem_header": (
                "theorem forall_or_distrib_left {α : Type} (P : Prop) (Q : α → Prop) : "
                "(∀ x : α, P ∨ Q x) → P ∨ (∀ x : α, Q x) :="
            ),
            "warmup_hint": (
                "Introduce `h` and immediately case-split on `Classical.em P` before introducing `x`! "
                "When `¬ P`, for any `x : α`, `h x` gives `P ∨ Q x`, contradicting `¬ P` on the left branch."
            ),
            "reference_sketchpad": (
                "Target: `(∀ x, P ∨ Q x) → P ∨ (∀ x, Q x)`.\n"
                "Notice we cannot constructively inspect `h x` before choosing `Or.inl` vs `Or.inr` because `α` might even be empty!\n"
                "Instead, use `Classical.em P` right after `intro h`:\n"
                "- Case `inl hp`: return `Or.inl hp`.\n"
                "- Case `inr hnp`: return `Or.inr (fun x => ...)`, where `rcases h x with hp | hqx` eliminates `hp` via `hnp hp` and returns `hqx`."
            ),
            "reference_proof": (
                "by\n"
                "  intro h\n"
                "  cases Classical.em P with\n"
                "  | inl hp => exact Or.inl hp\n"
                "  | inr hnp =>\n"
                "    apply Or.inr\n"
                "    intro x\n"
                "    rcases h x with hp | hqx\n"
                "    · exact False.elim (hnp hp)\n"
                "    · exact hqx"
            ),
        },
        # 4. Inductive Trees & Lists: Inorder Traversal of Mirrored Binary Tree
        {
            "id": "hq_04_btree_flatten_mirror",
            "domain": "inductive_ds",
            "title": "Inorder Flatten of Mirrored Binary Tree Reverses List",
            "preamble": (
                "inductive BTree (α : Type) where\n"
                "  | leaf : BTree α\n"
                "  | node : BTree α → α → BTree α → BTree α\n\n"
                "def mirrorT {α : Type} : BTree α → BTree α\n"
                "  | BTree.leaf => BTree.leaf\n"
                "  | BTree.node l v r => BTree.node (mirrorT r) v (mirrorT l)\n\n"
                "def flattenBT {α : Type} : BTree α → List α\n"
                "  | BTree.leaf => []\n"
                "  | BTree.node l v r => flattenBT l ++ [v] ++ flattenBT r"
            ),
            "theorem_header": (
                "theorem flattenBT_mirrorT {α : Type} (t : BTree α) : "
                "flattenBT (mirrorT t) = (flattenBT t).reverse :="
            ),
            "warmup_hint": (
                "Induct on `t : BTree α`. In the `node l v r ihl ihr` case, `simp [mirrorT, flattenBT, ihl, ihr, List.reverse_append, List.append_assoc]` "
                "handles reversing nested appends and `[v].reverse = [v]`."
            ),
            "reference_sketchpad": (
                "We induct structurally on `t : BTree α`.\n"
                "- Base `leaf`: `flattenBT (mirrorT leaf) = [] = [].reverse`.\n"
                "- Step `node l v r ihl ihr`: LHS is `flattenBT (mirrorT r) ++ [v] ++ flattenBT (mirrorT l)`, which by `ihr` and `ihl` equals `(flattenBT r).reverse ++ [v] ++ (flattenBT l).reverse`.\n"
                "  RHS is `(flattenBT l ++ [v] ++ flattenBT r).reverse`.\n"
                "  Using `List.reverse_append` and `List.append_assoc`, both sides normalize to `(flattenBT r).reverse ++ (v :: (flattenBT l).reverse)`!"
            ),
            "reference_proof": (
                "by\n"
                "  induction t with\n"
                "  | leaf => rfl\n"
                "  | node l v r ihl ihr =>\n"
                "    simp [mirrorT, flattenBT, ihl, ihr, List.reverse_append, List.append_assoc]"
            ),
        },
        # 5. Higher-Order Functions: Left Inverse + Injective Retraction => Bijection
        {
            "id": "hq_05_retraction_inj_right_inv",
            "domain": "logic_functions",
            "title": "Injective Left-Inverse Is Also a Two-Sided Inverse",
            "preamble": (
                "def InjFn {α β : Type} (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y\n"
                "def SurjFn {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y\n"
                "def LeftInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ x : α, g (f x) = x\n"
                "def RightInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ y : β, f (g y) = y"
            ),
            "theorem_header": (
                "theorem right_inv_and_surj_of_left_inv_inj {α β : Type} (f : α → β) (g : β → α) "
                "(hleft : LeftInvFn g f) (hinjg : InjFn g) : RightInvFn g f ∧ SurjFn f :="
            ),
            "warmup_hint": (
                "First prove `hr : RightInvFn g f` by taking `y : β`, applying `hinjg`, and using `hleft (g y) : g (f (g y)) = g y`. "
                "Then `SurjFn f` follows with witness `g y`."
            ),
            "reference_sketchpad": (
                "Given `hleft : ∀ x, g (f x) = x` and `hinjg : InjFn g`, we want `RightInvFn g f ∧ SurjFn f`.\n"
                "Key insight: to prove `f (g y) = y` for arbitrary `y : β`, apply `hinjg`! That reduces the goal to `g (f (g y)) = g y`, which is literally `hleft (g y)`!\n"
                "Once `hr : ∀ y, f (g y) = y` is established, `SurjFn f` holds with witness `⟨g y, hr y⟩`."
            ),
            "reference_proof": (
                "by\n"
                "  have hr : RightInvFn g f := by\n"
                "    intro y\n"
                "    exact hinjg (hleft (g y))\n"
                "  exact ⟨hr, fun y => ⟨g y, hr y⟩⟩"
            ),
        },
        # 6. Tail-Recursive Program Verification: `mapAcc` Accumulator Generalization
        {
            "id": "hq_06_mapAcc_correct",
            "domain": "inductive_ds",
            "title": "Tail-Recursive Map Accumulator Equivalence",
            "preamble": (
                "def mapAcc {α β : Type} (f : α → β) : List α → List β → List β\n"
                "  | [], acc => acc.reverse\n"
                "  | x :: xs, acc => mapAcc f xs (f x :: acc)"
            ),
            "theorem_header": (
                "theorem mapAcc_nil_eq_map {α β : Type} (f : α → β) (xs : List α) : "
                "mapAcc f xs [] = List.map f xs :="
            ),
            "warmup_hint": (
                "Prove helper `have haux : ∀ (ys : List α) (acc : List β), mapAcc f ys acc = acc.reverse ++ List.map f ys` "
                "by `induction ys generalizing acc`, using `List.reverse_cons` and `List.append_assoc`."
            ),
            "reference_sketchpad": (
                "Direct induction on `xs` with `acc = []` fails because `mapAcc f (x :: xs) []` calls `mapAcc f xs [f x]`.\n"
                "Generalize the accumulator! Define `haux : ∀ (ys : List α) (acc : List β), mapAcc f ys acc = acc.reverse ++ List.map f ys`.\n"
                "By `induction ys generalizing acc`:\n"
                "- `nil`: `acc.reverse = acc.reverse ++ []` via `simp`.\n"
                "- `cons y tl ih`: `mapAcc f (y :: tl) acc = mapAcc f tl (f y :: acc) = (f y :: acc).reverse ++ List.map f tl = (acc.reverse ++ [f y]) ++ List.map f tl = acc.reverse ++ (f y :: List.map f tl)`.\n"
                "Instantiate `haux xs []` to conclude!"
            ),
            "reference_proof": (
                "by\n"
                "  have haux : ∀ (ys : List α) (acc : List β), mapAcc f ys acc = acc.reverse ++ List.map f ys := by\n"
                "    intro ys\n"
                "    induction ys with\n"
                "    | nil => intro acc; simp [mapAcc]\n"
                "    | cons y tl ih =>\n"
                "      intro acc\n"
                "      simp [mapAcc, ih (f y :: acc), List.append_assoc]\n"
                "  simpa using haux xs []"
            ),
        },
        # 7. Heyting Algebra: Currying Law (a ⊓ b) ⇨ c = a ⇨ (b ⇨ c)
        {
            "id": "hq_07_heyting_curry",
            "domain": "order_lattice",
            "title": "Heyting Algebra Residuation Currying (a ⊓ b) ⇨ c = a ⇨ (b ⇨ c)",
            "preamble": (
                "class BoundedLattice (L : Type) where\n"
                "  le : L → L → Prop\n"
                "  bot : L\n"
                "  top : L\n"
                "  sup : L → L → L\n"
                "  inf : L → L → L\n"
                "  le_refl : ∀ a : L, le a a\n"
                "  le_trans : ∀ {a b c : L}, le a b → le b c → le a c\n"
                "  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b\n"
                "  bot_le : ∀ a : L, le bot a\n"
                "  le_top : ∀ a : L, le a top\n"
                "  le_sup_left : ∀ a b : L, le a (sup a b)\n"
                "  le_sup_right : ∀ a b : L, le b (sup a b)\n"
                "  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c\n"
                "  inf_le_left : ∀ a b : L, le (inf a b) a\n"
                "  inf_le_right : ∀ a b : L, le (inf a b) b\n"
                "  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)\n\n"
                "class HeytingAlg (H : Type) extends BoundedLattice H where\n"
                "  himp : H → H → H\n"
                "  le_himp_iff : ∀ a b c : H, BoundedLattice.le a (himp b c) ↔ BoundedLattice.le (BoundedLattice.inf a b) c"
            ),
            "theorem_header": (
                "theorem heyting_curry {H : Type} [HeytingAlg H] (a b c : H) : "
                "HeytingAlg.himp (BoundedLattice.inf a b) c = HeytingAlg.himp a (HeytingAlg.himp b c) :="
            ),
            "warmup_hint": (
                "Use `BoundedLattice.le_antisymm`. In one direction apply `le_himp_iff` twice so you need `inf (inf _ a) b ≤ c`, "
                "reassociating `inf (inf x a) b ≤ inf x (inf a b)` via `le_inf` and modus ponens. Do the reverse reassociation for the other direction."
            ),
            "reference_sketchpad": (
                "We prove `himp (inf a b) c = himp a (himp b c)` via `BoundedLattice.le_antisymm`.\n"
                "1. LHS ≤ RHS: apply `(le_himp_iff _ a _).mpr` then `(le_himp_iff _ b c).mpr`. Goal: `inf (inf (himp (inf a b) c) a) b ≤ c`.\n"
                "   Show `inf (inf x a) b ≤ inf x (inf a b)` via `le_inf`, then chain with modus ponens `inf (himp (inf a b) c) (inf a b) ≤ c`!\n"
                "2. RHS ≤ LHS: apply `(le_himp_iff _ (inf a b) c).mpr`. Goal: `inf (himp a (himp b c)) (inf a b) ≤ c`.\n"
                "   First show `inf y (inf a b) ≤ inf (inf y a) b`, then `inf (inf y a) b ≤ inf (himp b c) b ≤ c` using modus ponens twice!"
            ),
            "reference_proof": (
                "by\n"
                "  apply BoundedLattice.le_antisymm\n"
                "  · apply (HeytingAlg.le_himp_iff _ a _).mpr\n"
                "    apply (HeytingAlg.le_himp_iff _ b c).mpr\n"
                "    have hassoc1 : BoundedLattice.le "
                "(BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) a) b) "
                "(BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) (BoundedLattice.inf a b)) := by\n"
                "      apply BoundedLattice.le_inf\n"
                "      · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_left _ _)\n"
                "      · apply BoundedLattice.le_inf\n"
                "        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_right _ _)\n"
                "        · exact BoundedLattice.inf_le_right _ _\n"
                "    have hmp : BoundedLattice.le "
                "(BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) (BoundedLattice.inf a b)) c := "
                "(HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)\n"
                "    exact BoundedLattice.le_trans hassoc1 hmp\n"
                "  · apply (HeytingAlg.le_himp_iff _ (BoundedLattice.inf a b) c).mpr\n"
                "    have hmp1 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) a) (HeytingAlg.himp b c) := "
                "(HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)\n"
                "    have hstep : BoundedLattice.le "
                "(BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) (BoundedLattice.inf a b)) "
                "(BoundedLattice.inf (HeytingAlg.himp b c) b) := by\n"
                "      apply BoundedLattice.le_inf\n"
                "      · have hl : BoundedLattice.le "
                "(BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) (BoundedLattice.inf a b)) "
                "(BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) a) := by\n"
                "          apply BoundedLattice.le_inf (BoundedLattice.inf_le_left _ _)\n"
                "          exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) (BoundedLattice.inf_le_left _ _)\n"
                "        exact BoundedLattice.le_trans hl hmp1\n"
                "      · exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) (BoundedLattice.inf_le_right _ _)\n"
                "    have hmp2 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp b c) b) c := "
                "(HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)\n"
                "    exact BoundedLattice.le_trans hstep hmp2"
            ),
        },
        # 8. Rewriting Systems: Diamond Property Strip Lemma
        {
            "id": "hq_08_diamond_strip_lemma",
            "domain": "relations_sets",
            "title": "Church-Rosser Diamond Strip Lemma",
            "preamble": (
                "inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where\n"
                "  | refl (x : α) : StarStep R x x\n"
                "  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z\n\n"
                "def Diamond {α : Type} (R : α → α → Prop) : Prop :=\n"
                "  ∀ {x y z : α}, R x y → R x z → ∃ w : α, R y w ∧ R z w"
            ),
            "theorem_header": (
                "theorem diamond_strip {α : Type} (R : α → α → Prop) (hdiam : Diamond R) "
                "{x y z : α} (hxy : R x y) (hxz : StarStep R x z) : "
                "∃ w : α, StarStep R y w ∧ R z w :="
            ),
            "warmup_hint": (
                "Run `induction hxz generalizing y`. In `refl`, pick witness `y`. In `step hxu _ ih`, "
                "apply `hdiam hxy hxu` to get `⟨v, hyv, huv⟩`, then apply `ih huv` to get `⟨w, hvw, hzw⟩`."
            ),
            "reference_sketchpad": (
                "To prove the strip lemma from `Diamond R`, induct on the multi-step derivation `hxz : StarStep R x z` **generalizing `y`**!\n"
                "- Base `refl x`: we have `hxy : R x y`, need `∃ w, StarStep R y w ∧ R x w`. Witness `w = y` gives `⟨y, StarStep.refl y, hxy⟩`!\n"
                "- Step `step hxu h_uz ih`: apply `hdiam hxy hxu` to obtain `⟨v, hyv, huv⟩`.\n"
                "  Now feed `huv : R u v` into `ih` to obtain `⟨w, hvw, hzw⟩`.\n"
                "  Prepend `hyv` onto `hvw` with `StarStep.step hyv hvw`, yielding `⟨w, StarStep.step hyv hvw, hzw⟩`!"
            ),
            "reference_proof": (
                "by\n"
                "  induction hxz generalizing y with\n"
                "  | refl _ => exact ⟨y, StarStep.refl y, hxy⟩\n"
                "  | step hxu _ ih =>\n"
                "    rcases hdiam hxy hxu with ⟨v, hyv, huv⟩\n"
                "    rcases ih huv with ⟨w, hvw, hzw⟩\n"
                "    exact ⟨w, StarStep.step hyv hvw, hzw⟩"
            ),
        },
        # 9. Number Theory: 3 Divides n^3 + 2n for all n
        {
            "id": "hq_09_div3_cube_plus_2n",
            "domain": "nat_number_theory",
            "title": "Divisibility of n^3 + 2n by 3",
            "preamble": "def PureDvd (d n : Nat) : Prop := ∃ k : Nat, n = d * k",
            "theorem_header": (
                "theorem dvd3_cube_add_two_mul (n : Nat) : PureDvd 3 (n * n * n + 2 * n) :="
            ),
            "warmup_hint": (
                "Induct on `n`. In `succ k ih`, unpack `⟨m, hm⟩ := ih` and choose witness `m + (k * k + k + 1)`. "
                "First expand `(k + 1) * (k + 1) = k * k + 2 * k + 1`, then multiply by `(k + 1)` using `Nat.right_distrib` and `Nat.left_distrib`, and finish with `omega`."
            ),
            "reference_sketchpad": (
                "We prove `∃ m, n^3 + 2n = 3 * m` by induction on `n`.\n"
                "- `zero`: witness `0` works by `rfl`.\n"
                "- `succ k ih`: unpack `⟨m, hm⟩ := ih`, where `k * k * k + 2 * k = 3 * m`.\n"
                "  First prove `hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1`.\n"
                "  Then expand `(k + 1) * (k + 1) * (k + 1) = (k * k + 2 * k + 1) * (k + 1)` via `Nat.left_distrib` and `Nat.right_distrib`, reassociating `2 * k * k = 2 * (k * k)`.\n"
                "  With witness `m + (k * k + k + 1)`, `omega` finishes immediately!"
            ),
            "reference_proof": (
                "by\n"
                "  induction n with\n"
                "  | zero => exact ⟨0, rfl⟩\n"
                "  | succ k ih =>\n"
                "    rcases ih with ⟨m, hm⟩\n"
                "    refine ⟨m + (k * k + k + 1), ?_⟩\n"
                "    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by\n"
                "      rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]\n"
                "      omega\n"
                "    have hcb : (k + 1) * (k + 1) * (k + 1) = k * k * k + 3 * (k * k) + 3 * k + 1 := by\n"
                "      rw [hsq, Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]\n"
                "      rw [Nat.mul_assoc 2 k k]\n"
                "      omega\n"
                "    omega"
            ),
        },
        # 10. Pure Ring Theory: (-a) * (-b) = a * b
        {
            "id": "hq_10_ring_neg_mul_neg",
            "domain": "algebra",
            "title": "Product of Two Negatives in a Ring: (-a) * (-b) = a * b",
            "preamble": (
                "class PureRing (R : Type) where\n"
                "  add : R → R → R\n"
                "  zero : R\n"
                "  neg : R → R\n"
                "  mul : R → R → R\n"
                "  one : R\n"
                "  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)\n"
                "  zero_add : ∀ a : R, add zero a = a\n"
                "  add_zero : ∀ a : R, add a zero = a\n"
                "  neg_add : ∀ a : R, add (neg a) a = zero\n"
                "  add_neg : ∀ a : R, add a (neg a) = zero\n"
                "  add_comm : ∀ a b : R, add a b = add b a\n"
                "  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)\n"
                "  one_mul : ∀ a : R, mul one a = a\n"
                "  mul_one : ∀ a : R, mul a one = a\n"
                "  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)\n"
                "  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)"
            ),
            "theorem_header": (
                "theorem ring_neg_mul_neg {R : Type} [PureRing R] (a b : R) : "
                "PureRing.mul (PureRing.neg a) (PureRing.neg b) = PureRing.mul a b :="
            ),
            "warmup_hint": (
                "Show both `mul (neg a) (neg b)` and `mul a b` add with `mul (neg a) b` to give `zero`: "
                "`add (mul (neg a) b) (mul (neg a) (neg b)) = mul (neg a) zero = zero`, and "
                "`add (mul (neg a) b) (mul a b) = mul zero b = zero`. Then left-cancel `mul (neg a) b`!"
            ),
            "reference_sketchpad": (
                "Elegant cancellation proof of `(-a) * (-b) = a * b` from raw `PureRing` axioms:\n"
                "Compare `add (mul (neg a) b) (mul (neg a) (neg b))` with `add (mul (neg a) b) (mul a b)`!\n"
                "1. First prove `hz_r : mul (neg a) zero = zero` and `hz_l : mul zero b = zero`.\n"
                "2. LHS: `add (mul (neg a) b) (mul (neg a) (neg b)) = mul (neg a) (add b (neg b)) = mul (neg a) zero = zero`.\n"
                "3. RHS: `add (mul (neg a) b) (mul a b) = mul (add (neg a) a) b = mul zero b = zero`.\n"
                "4. Equate LHS = RHS and add `neg (mul (neg a) b)` on the left to cancel `mul (neg a) b`!"
            ),
            "reference_proof": (
                "by\n"
                "  have hz_r : PureRing.mul (PureRing.neg a) PureRing.zero = PureRing.zero := by\n"
                "    have h0 : PureRing.add (PureRing.mul (PureRing.neg a) PureRing.zero) (PureRing.mul (PureRing.neg a) PureRing.zero) = "
                "PureRing.add (PureRing.mul (PureRing.neg a) PureRing.zero) PureRing.zero := by\n"
                "      rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]\n"
                "    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul (PureRing.neg a) PureRing.zero))) h0\n"
                "    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'\n"
                "    exact h0'\n"
                "  have hz_l : PureRing.mul PureRing.zero b = PureRing.zero := by\n"
                "    have h0 : PureRing.add (PureRing.mul PureRing.zero b) (PureRing.mul PureRing.zero b) = "
                "PureRing.add (PureRing.mul PureRing.zero b) PureRing.zero := by\n"
                "      rw [← PureRing.right_distrib, PureRing.zero_add, PureRing.add_zero]\n"
                "    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul PureRing.zero b))) h0\n"
                "    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'\n"
                "    exact h0'\n"
                "  have heq : PureRing.add (PureRing.mul (PureRing.neg a) b) (PureRing.mul (PureRing.neg a) (PureRing.neg b)) = "
                "PureRing.add (PureRing.mul (PureRing.neg a) b) (PureRing.mul a b) := by\n"
                "    rw [← PureRing.left_distrib, PureRing.add_neg, hz_r, ← PureRing.right_distrib, PureRing.neg_add, hz_l]\n"
                "  have hfin := congrArg (PureRing.add (PureRing.neg (PureRing.mul (PureRing.neg a) b))) heq\n"
                "  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at hfin\n"
                "  exact hfin"
            ),
        },
        # 11. Functional Programming: Higher-Order CPS Duality between foldr and foldl
        {
            "id": "hq_11_foldl_via_foldr_cps",
            "domain": "inductive_ds",
            "title": "Continuation-Passing Expressibility of foldl via foldr",
            "preamble": (
                "def foldrL {α β : Type} (f : α → β → β) (z : β) : List α → β\n"
                "  | [] => z\n"
                "  | x :: xs => f x (foldrL f z xs)\n\n"
                "def foldlL {α β : Type} (f : β → α → β) : β → List α → β\n"
                "  | acc, [] => acc\n"
                "  | acc, x :: xs => foldlL f (f acc x) xs"
            ),
            "theorem_header": (
                "theorem foldl_eq_foldr_cps {α β : Type} (f : β → α → β) (xs : List α) (acc : β) : "
                "foldrL (fun x k a => k (f a x)) (fun a => a) xs acc = foldlL f acc xs :="
            ),
            "warmup_hint": (
                "Induct on `xs generalizing acc`! In `nil`, both sides evaluate to `acc` by `rfl`. "
                "In `cons x tl ih`, unfold `foldrL` and `foldlL` and apply `ih (f acc x)`."
            ),
            "reference_sketchpad": (
                "Look at `foldrL (fun x k a => k (f a x)) (fun a => a) xs acc = foldlL f acc xs`.\n"
                "Because `foldrL` builds a function `β → β` that is then applied to `acc`, in the `cons x tl` step:\n"
                "`foldrL step id (x :: tl) acc` reduces to `(fun k a => k (f a x)) (foldrL step id tl) acc`, which beta-reduces to `foldrL step id tl (f acc x)`!\n"
                "Meanwhile `foldlL f acc (x :: tl)` reduces to `foldlL f (f acc x) tl`.\n"
                "So `induction xs generalizing acc` closes immediately via `ih (f acc x)`!"
            ),
            "reference_proof": (
                "by\n"
                "  induction xs generalizing acc with\n"
                "  | nil => rfl\n"
                "  | cons x tl ih =>\n"
                "    simp only [foldrL, foldlL]\n"
                "    exact ih (f acc x)"
            ),
        },
        # 12. Group Commutator Inverse: (a b a⁻¹ b⁻¹)⁻¹ = b a b⁻¹ a⁻¹
        {
            "id": "hq_12_group_commutator_inv",
            "domain": "algebra",
            "title": "Inverse of a Group Commutator [a, b]⁻¹ = [b, a]",
            "preamble": (
                "class PureGroup (G : Type) where\n"
                "  mul : G → G → G\n"
                "  one : G\n"
                "  inv : G → G\n"
                "  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)\n"
                "  one_mul : ∀ a : G, mul one a = a\n"
                "  mul_one : ∀ a : G, mul a one = a\n"
                "  inv_mul : ∀ a : G, mul (inv a) a = one\n"
                "  mul_inv : ∀ a : G, mul a (inv a) = one\n\n"
                "def commG {G : Type} [PureGroup G] (a b : G) : G :=\n"
                "  PureGroup.mul (PureGroup.mul (PureGroup.mul a b) (PureGroup.inv a)) (PureGroup.inv b)"
            ),
            "theorem_header": (
                "theorem commG_inv {G : Type} [PureGroup G] (a b : G) : "
                "PureGroup.inv (commG a b) = commG b a :="
            ),
            "warmup_hint": (
                "Show `PureGroup.mul (commG a b) (commG b a) = PureGroup.one` by canceling the inner pairs "
                "`inv b * b`, `inv a * a`, `b * inv b`, and `a * inv a`. Equate with `mul_inv (commG a b)` and left-cancel `commG a b`!"
            ),
            "reference_sketchpad": (
                "Instead of proving `inv_mul_rev` four times, use uniqueness of right-inverses!\n"
                "Compute `mul (commG a b) (commG b a)`:\n"
                "`((a * b * a⁻¹) * b⁻¹) * (((b * a) * b⁻¹) * a⁻¹)`.\n"
                "Cancel from the middle outward:\n"
                "1. `b⁻¹ * b = 1` leaves `(a * b * a⁻¹) * (a * b⁻¹ * a⁻¹)`.\n"
                "2. `a⁻¹ * a = 1` leaves `(a * b) * (b⁻¹ * a⁻¹)`.\n"
                "3. `b * b⁻¹ = 1` leaves `a * a⁻¹ = 1`!\n"
                "Since `mul (commG a b) (inv (commG a b)) = one` as well, left-canceling `commG a b` proves `inv (commG a b) = commG b a`!"
            ),
            "reference_proof": (
                "by\n"
                "  have cancel_mid : ∀ x y z : G, PureGroup.mul (PureGroup.mul x y) (PureGroup.mul (PureGroup.inv y) z) = PureGroup.mul x z := by\n"
                "    intro x y z\n"
                "    rw [PureGroup.mul_assoc x y (PureGroup.mul (PureGroup.inv y) z)]\n"
                "    rw [← PureGroup.mul_assoc y (PureGroup.inv y) z, PureGroup.mul_inv, PureGroup.one_mul]\n"
                "  have cancel_mid_inv : ∀ x y z : G, PureGroup.mul (PureGroup.mul x (PureGroup.inv y)) (PureGroup.mul y z) = PureGroup.mul x z := by\n"
                "    intro x y z\n"
                "    rw [PureGroup.mul_assoc x (PureGroup.inv y) (PureGroup.mul y z)]\n"
                "    rw [← PureGroup.mul_assoc (PureGroup.inv y) y z, PureGroup.inv_mul, PureGroup.one_mul]\n"
                "  have hprod : PureGroup.mul (commG a b) (commG b a) = PureGroup.one := by\n"
                "    unfold commG\n"
                "    have s1 : PureGroup.mul (PureGroup.mul (PureGroup.mul b a) (PureGroup.inv b)) (PureGroup.inv a) = "
                "PureGroup.mul b (PureGroup.mul a (PureGroup.mul (PureGroup.inv b) (PureGroup.inv a))) := by\n"
                "      rw [PureGroup.mul_assoc, PureGroup.mul_assoc]\n"
                "    rw [s1, cancel_mid_inv, cancel_mid_inv, cancel_mid, PureGroup.mul_inv]\n"
                "  calc PureGroup.inv (commG a b)\n"
                "    _ = PureGroup.mul (PureGroup.inv (commG a b)) PureGroup.one := by rw [PureGroup.mul_one]\n"
                "    _ = PureGroup.mul (PureGroup.inv (commG a b)) (PureGroup.mul (commG a b) (commG b a)) := by rw [hprod]\n"
                "    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (commG a b)) (commG a b)) (commG b a) := by rw [← PureGroup.mul_assoc]\n"
                "    _ = commG b a := by rw [PureGroup.inv_mul, PureGroup.one_mul]"
            ),
        },
        # 13. Fibonacci Two-Variable Addition Law
        {
            "id": "hq_13_fib_addition_formula",
            "domain": "nat_number_theory",
            "title": "Fibonacci Addition Identity F_{m+n+1} = F_m F_n + F_{m+1} F_{n+1}",
            "preamble": (
                "def fibN : Nat → Nat\n"
                "  | 0 => 0\n"
                "  | 1 => 1\n"
                "  | n + 2 => fibN n + fibN (n + 1)"
            ),
            "theorem_header": (
                "theorem fibN_add_succ (m n : Nat) : "
                "fibN (m + n + 1) = fibN m * fibN n + fibN (m + 1) * fibN (n + 1) :="
            ),
            "warmup_hint": (
                "Induct on `n generalizing m`! For `n = 0`, `simp [fibN]`. For `n = k + 1`, specialize `ih (m + 1)` "
                "since `(m + 1) + k + 1 = m + (k + 1) + 1`, unfold `fibN (m + 2)` and `fibN (k + 2)`, expand with `Nat.left_distrib`/`Nat.right_distrib`, and finish with `omega`."
            ),
            "reference_sketchpad": (
                "Trick for `fibN (m + n + 1) = fibN m * fibN n + fibN (m + 1) * fibN (n + 1)`:\n"
                "Instead of two-step induction on `n`, induct single-step on `n` **generalizing `m`**!\n"
                "- Base `n = 0`: `fibN (m + 1) = fibN m * 0 + fibN (m + 1) * 1`, which holds by `simp [fibN]`.\n"
                "- Step `n = k + 1`: notice `m + (k + 1) + 1 = (m + 1) + k + 1`!\n"
                "  Apply `ih (m + 1)`! That gives `fibN ((m + 1) + k + 1) = fibN (m + 1) * fibN k + fibN (m + 2) * fibN (k + 1)`.\n"
                "  Unfold `fibN (m + 2) = fibN m + fibN (m + 1)` and `fibN (k + 2) = fibN k + fibN (k + 1)`, expand products with `Nat.right_distrib` and `Nat.left_distrib`, and close with `omega`!"
            ),
            "reference_proof": (
                "by\n"
                "  induction n generalizing m with\n"
                "  | zero => simp [fibN]\n"
                "  | succ k ih =>\n"
                "    have hshift : m + (k + 1) + 1 = (m + 1) + k + 1 := by omega\n"
                "    rw [hshift, ih (m + 1)]\n"
                "    have hm2 : fibN (m + 1 + 1) = fibN m + fibN (m + 1) := rfl\n"
                "    have hk2 : fibN (k + 1 + 1) = fibN k + fibN (k + 1) := rfl\n"
                "    rw [hm2, hk2, Nat.right_distrib, Nat.left_distrib]\n"
                "    omega"
            ),
        },
        # 14. Compiler Verification: Stack Machine with Addition and Multiplication
        {
            "id": "hq_14_arith_vm_compiler",
            "domain": "inductive_ds",
            "title": "Stack Virtual Machine Compiler Correctness for Add + Mul AST",
            "preamble": (
                "inductive ArithAST where\n"
                "  | lit : Nat → ArithAST\n"
                "  | add : ArithAST → ArithAST → ArithAST\n"
                "  | mul : ArithAST → ArithAST → ArithAST\n\n"
                "def evalAST : ArithAST → Nat\n"
                "  | ArithAST.lit n => n\n"
                "  | ArithAST.add e1 e2 => evalAST e1 + evalAST e2\n"
                "  | ArithAST.mul e1 e2 => evalAST e1 * evalAST e2\n\n"
                "inductive OpInstr where\n"
                "  | push : Nat → OpInstr\n"
                "  | addOp : OpInstr\n"
                "  | mulOp : OpInstr\n\n"
                "def execOps : List OpInstr → List Nat → List Nat\n"
                "  | [], stk => stk\n"
                "  | OpInstr.push n :: ops, stk => execOps ops (n :: stk)\n"
                "  | OpInstr.addOp :: ops, b :: a :: stk => execOps ops ((a + b) :: stk)\n"
                "  | OpInstr.addOp :: ops, stk => execOps ops stk\n"
                "  | OpInstr.mulOp :: ops, b :: a :: stk => execOps ops ((a * b) :: stk)\n"
                "  | OpInstr.mulOp :: ops, stk => execOps ops stk\n\n"
                "def compileAST : ArithAST → List OpInstr\n"
                "  | ArithAST.lit n => [OpInstr.push n]\n"
                "  | ArithAST.add e1 e2 => compileAST e1 ++ compileAST e2 ++ [OpInstr.addOp]\n"
                "  | ArithAST.mul e1 e2 => compileAST e1 ++ compileAST e2 ++ [OpInstr.mulOp]"
            ),
            "theorem_header": (
                "theorem compileAST_correct (e : ArithAST) (stk : List Nat) : "
                "execOps (compileAST e) stk = evalAST e :: stk :="
            ),
            "warmup_hint": (
                "First prove `hexec : ∀ (c1 c2 : List OpInstr) (s : List Nat), execOps (c1 ++ c2) s = execOps c2 (execOps c1 s)` "
                "by induction on `c1` splitting on `push`/`addOp`/`mulOp` and stack depth `0, 1, ≥2`. Then induct on `e generalizing stk`."
            ),
            "reference_sketchpad": (
                "1. Prove sequential composition `hexec : execOps (c1 ++ c2) s = execOps c2 (execOps c1 s)` by induction on `c1 generalizing s`.\n"
                "   For both `addOp` and `mulOp`, split stack `s` into `[]`, `[b]`, and `b :: a :: s'` so `execOps` reduces definitionally.\n"
                "2. Induct on `e : ArithAST generalizing stk`:\n"
                "   - `lit n`: `rfl`.\n"
                "   - `add e1 e2 ih1 ih2`: rewrite `List.append_assoc`, `hexec`, `ih1`, `hexec`, `ih2`.\n"
                "   - `mul e1 e2 ih1 ih2`: identical rewrite sequence producing `(evalAST e1 * evalAST e2) :: stk`!"
            ),
            "reference_proof": (
                "by\n"
                "  have hexec : ∀ (c1 c2 : List OpInstr) (s : List Nat), execOps (c1 ++ c2) s = execOps c2 (execOps c1 s) := by\n"
                "    intro c1 c2\n"
                "    induction c1 with\n"
                "    | nil => intro s; rfl\n"
                "    | cons op rest ih =>\n"
                "      intro s\n"
                "      cases op with\n"
                "      | push n => exact ih (n :: s)\n"
                "      | addOp =>\n"
                "        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩\n"
                "        · exact ih []\n"
                "        · exact ih [b]\n"
                "        · exact ih ((a + b) :: s')\n"
                "      | mulOp =>\n"
                "        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩\n"
                "        · exact ih []\n"
                "        · exact ih [b]\n"
                "        · exact ih ((a * b) :: s')\n"
                "  induction e generalizing stk with\n"
                "  | lit n => rfl\n"
                "  | add e1 e2 ih1 ih2 =>\n"
                "    simp only [compileAST, evalAST]\n"
                "    rw [List.append_assoc, hexec, ih1, hexec, ih2]\n"
                "    rfl\n"
                "  | mul e1 e2 ih1 ih2 =>\n"
                "    simp only [compileAST, evalAST]\n"
                "    rw [List.append_assoc, hexec, ih1, hexec, ih2]\n"
                "    rfl"
            ),
        },
        # 15. Number Theory: Nicomachus's Sum of Cubes Theorem
        {
            "id": "hq_15_nicomachus_sum_cubes",
            "domain": "nat_number_theory",
            "title": "Nicomachus's Sum of Cubes Identity 4 * Σ k^3 = (n(n+1))^2",
            "preamble": (
                "def sumCubes : Nat → Nat\n"
                "  | 0 => 0\n"
                "  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)"
            ),
            "theorem_header": (
                "theorem nicomachus_sum_cubes (n : Nat) : "
                "4 * sumCubes n = (n * (n + 1)) * (n * (n + 1)) :="
            ),
            "warmup_hint": (
                "Induct on `n`. In `succ k ih`, rewrite `sumCubes`, `Nat.left_distrib`, and `ih`. "
                "Factor `(k + 1) * (k + 2) = k * (k + 1) + 2 * (k + 1)`, expand `(A + B) * (A + B)` where `A = k * (k + 1)` and `B = 2 * (k + 1)`, "
                "and show `2 * A * B + B * B = 4 * ((k + 1) * (k + 1) * (k + 1))`."
            ),
            "reference_sketchpad": (
                "Goal: `4 * sumCubes n = (n * (n + 1)) * (n * (n + 1))` without Mathlib's `ring`!\n"
                "Smart factorization trick for the inductive step `n = k + 1`:\n"
                "Notice `(k + 1) * (k + 2) = (k + 1) * k + (k + 1) * 2`.\n"
                "Even simpler: factor out `(k + 1) * (k + 1)` on BOTH sides of the inductive step!\n"
                "Wait: in `ih`, `(k * (k + 1)) * (k * (k + 1)) = (k * k) * ((k + 1) * (k + 1))`, and `4 * ((k + 1) * (k + 1) * (k + 1)) = (4 * (k + 1)) * ((k + 1) * (k + 1))`!\n"
                "Wait — `(k * k + 4 * k + 4) = (k + 2) * (k + 2)`!! Let's check:\n"
                "Let `S = (k + 1) * (k + 1)`.\n"
                "- `(k * (k + 1)) * (k * (k + 1)) = (k * k) * S`.\n"
                "- `4 * ((k + 1) * (k + 1) * (k + 1)) = (4 * (k + 1)) * S`.\n"
                "- `((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) = ((k + 2) * (k + 2)) * S`.\n"
                "And `k * k + 4 * (k + 1) = (k + 2) * (k + 2)` is trivial by `Nat.left_distrib`/`Nat.right_distrib` + `omega`!"
            ),
            "reference_proof": (
                "by\n"
                "  induction n with\n"
                "  | zero => rfl\n"
                "  | succ k ih =>\n"
                "    rw [sumCubes, Nat.left_distrib, ih]\n"
                "    have h1 : (k * (k + 1)) * (k * (k + 1)) = (k * k) * ((k + 1) * (k + 1)) := by\n"
                "      rw [Nat.mul_assoc, ← Nat.mul_assoc (k + 1) k (k + 1), Nat.mul_comm (k + 1) k, Nat.mul_assoc, ← Nat.mul_assoc]\n"
                "    have h2 : 4 * ((k + 1) * (k + 1) * (k + 1)) = (4 * (k + 1)) * ((k + 1) * (k + 1)) := by\n"
                "      rw [Nat.mul_comm ((k + 1) * (k + 1)) (k + 1), ← Nat.mul_assoc]\n"
                "    have h3 : ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) = ((k + 2) * (k + 2)) * ((k + 1) * (k + 1)) := by\n"
                "      rw [Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, ← Nat.mul_assoc (k + 1) (k + 2) (k + 1)]\n"
                "      rw [Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, ← Nat.mul_assoc]\n"
                "    have h4 : k * k + 4 * (k + 1) = (k + 2) * (k + 2) := by\n"
                "      rw [Nat.left_distrib (k + 2) k 2, Nat.right_distrib, Nat.right_distrib]\n"
                "      omega\n"
                "    rw [h1, h2, h3, ← Nat.right_distrib, h4]"
            ),
        },
    ]


def build_eval_holdout_questions() -> List[Dict]:
    """12 completely unseen pure Lean 4 theorems across all 6 domains for objective evaluation."""
    return [
        {
            "id": "eval_01_unique_identity",
            "domain": "algebra",
            "title": "Uniqueness of Two-Sided Monoid Identity",
            "preamble": (
                "class PureMonoid (M : Type) where\n"
                "  mul : M → M → M\n"
                "  one : M\n"
                "  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)\n"
                "  one_mul : ∀ a : M, mul one a = a\n"
                "  mul_one : ∀ a : M, mul a one = a"
            ),
            "theorem_header": (
                "theorem unique_left_id {M : Type} [PureMonoid M] (e : M) "
                "(he : ∀ x : M, PureMonoid.mul e x = x) : e = PureMonoid.one :="
            ),
            "reference_sketchpad": "Evaluate `he PureMonoid.one` to get `mul e one = one`, and simplify `mul e one` to `e` via `PureMonoid.mul_one`.",
            "reference_proof": "by\n  have h := he PureMonoid.one\n  rw [PureMonoid.mul_one] at h\n  exact h",
        },
        {
            "id": "eval_02_group_unique_inv",
            "domain": "algebra",
            "title": "Uniqueness of Right Inverse in a Group",
            "preamble": (
                "class PureGroup (G : Type) where\n"
                "  mul : G → G → G\n"
                "  one : G\n"
                "  inv : G → G\n"
                "  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)\n"
                "  one_mul : ∀ a : G, mul one a = a\n"
                "  mul_one : ∀ a : G, mul a one = a\n"
                "  inv_mul : ∀ a : G, mul (inv a) a = one\n"
                "  mul_inv : ∀ a : G, mul a (inv a) = one"
            ),
            "theorem_header": (
                "theorem unique_right_inv {G : Type} [PureGroup G] (a b : G) "
                "(h : PureGroup.mul a b = PureGroup.one) : b = PureGroup.inv a :="
            ),
            "reference_sketchpad": "Multiply `h` on the left by `inv a`, reassociate via `← mul_assoc`, and simplify `inv a * a = one` and `inv a * one = inv a`.",
            "reference_proof": (
                "by\n"
                "  have h1 := congrArg (PureGroup.mul (PureGroup.inv a)) h\n"
                "  rw [← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.mul_one] at h1\n"
                "  exact h1"
            ),
        },
        {
            "id": "eval_03_lattice_sup_assoc",
            "domain": "order_lattice",
            "title": "Associativity of Join in a Pure Lattice",
            "preamble": (
                "class PureLattice (L : Type) where\n"
                "  le : L → L → Prop\n"
                "  sup : L → L → L\n"
                "  inf : L → L → L\n"
                "  le_refl : ∀ a : L, le a a\n"
                "  le_trans : ∀ {a b c : L}, le a b → le b c → le a c\n"
                "  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b\n"
                "  le_sup_left : ∀ a b : L, le a (sup a b)\n"
                "  le_sup_right : ∀ a b : L, le b (sup a b)\n"
                "  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c"
            ),
            "theorem_header": (
                "theorem sup_assoc_pure {L : Type} [PureLattice L] (a b c : L) : "
                "PureLattice.sup (PureLattice.sup a b) c = PureLattice.sup a (PureLattice.sup b c) :="
            ),
            "reference_sketchpad": "Apply `le_antisymm`; in both directions use nested `sup_le` together with `le_sup_left`, `le_sup_right`, and `le_trans`.",
            "reference_proof": (
                "by\n"
                "  apply PureLattice.le_antisymm\n"
                "  · apply PureLattice.sup_le\n"
                "    · apply PureLattice.sup_le (PureLattice.le_sup_left _ _)\n"
                "      exact PureLattice.le_trans (PureLattice.le_sup_left b c) (PureLattice.le_sup_right a _)\n"
                "    · exact PureLattice.le_trans (PureLattice.le_sup_right b c) (PureLattice.le_sup_right a _)\n"
                "  · apply PureLattice.sup_le\n"
                "    · exact PureLattice.le_trans (PureLattice.le_sup_left a b) (PureLattice.le_sup_left _ c)\n"
                "    · apply PureLattice.sup_le\n"
                "      · exact PureLattice.le_trans (PureLattice.le_sup_right a b) (PureLattice.le_sup_left _ c)\n"
                "      · exact PureLattice.le_sup_right _ c"
            ),
        },
        {
            "id": "eval_04_closure_inf_closed",
            "domain": "order_lattice",
            "title": "Meet of Two Closure-Fixed Elements Is Fixed",
            "preamble": (
                "class PureLattice (L : Type) where\n"
                "  le : L → L → Prop\n"
                "  inf : L → L → L\n"
                "  le_refl : ∀ a : L, le a a\n"
                "  le_trans : ∀ {a b c : L}, le a b → le b c → le a c\n"
                "  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b\n"
                "  inf_le_left : ∀ a b : L, le (inf a b) a\n"
                "  inf_le_right : ∀ a b : L, le (inf a b) b\n"
                "  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)\n\n"
                "structure ClosureOp (L : Type) [PureLattice L] (cl : L → L) : Prop where\n"
                "  extensive : ∀ x, PureLattice.le x (cl x)\n"
                "  monotone : ∀ {x y}, PureLattice.le x y → PureLattice.le (cl x) (cl y)\n"
                "  idempotent : ∀ x, cl (cl x) = cl x"
            ),
            "theorem_header": (
                "theorem closed_inf_closed {L : Type} [PureLattice L] (cl : L → L) (hcl : ClosureOp L cl) "
                "(a b : L) (ha : cl a = a) (hb : cl b = b) : "
                "cl (PureLattice.inf a b) = PureLattice.inf a b :="
            ),
            "reference_sketchpad": "Use `le_antisymm`. For `cl (inf a b) ≤ inf a b`, apply `le_inf`; by monotonicity `cl (inf a b) ≤ cl a = a` and `cl (inf a b) ≤ cl b = b`. Reverse direction is `hcl.extensive`.",
            "reference_proof": (
                "by\n"
                "  apply PureLattice.le_antisymm\n"
                "  · apply PureLattice.le_inf\n"
                "    · have h1 := hcl.monotone (PureLattice.inf_le_left a b)\n"
                "      rw [ha] at h1; exact h1\n"
                "    · have h2 := hcl.monotone (PureLattice.inf_le_right a b)\n"
                "      rw [hb] at h2; exact h2\n"
                "  · exact hcl.extensive _"
            ),
        },
        {
            "id": "eval_05_preimg_compl",
            "domain": "relations_sets",
            "title": "Preimage Commutes with Set Complement",
            "preamble": (
                "def SetP (α : Type) := α → Prop\n"
                "def ComplP {α : Type} (S : SetP α) : SetP α := fun x => ¬ S x\n"
                "def PreimgP {α β : Type} (f : α → β) (T : SetP β) : SetP α := fun x => T (f x)"
            ),
            "theorem_header": (
                "theorem preimg_compl_eq {α β : Type} (f : α → β) (T : SetP β) : "
                "PreimgP f (ComplP T) = ComplP (PreimgP f T) :="
            ),
            "reference_sketchpad": "Both sides are definitionally `fun x => ¬ T (f x)`, so `rfl` proves equality directly!",
            "reference_proof": "by\n  rfl",
        },
        {
            "id": "eval_06_star_reverse_ind",
            "domain": "relations_sets",
            "title": "Converse Commutes with Reflexive-Transitive Closure",
            "preamble": (
                "inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where\n"
                "  | refl (x : α) : StarStep R x x\n"
                "  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z\n\n"
                "def Conv (R : α → α → Prop) : α → α → Prop := fun x y => R y x"
            ),
            "theorem_header": (
                "theorem star_conv_imp {α : Type} (R : α → α → Prop) {x y : α} "
                "(h : StarStep R x y) : StarStep (Conv R) y x :="
            ),
            "reference_sketchpad": "Prove helper `hsnoc` appending a single `Conv R` step on the right, then induct on `h : StarStep R x y`.",
            "reference_proof": (
                "by\n"
                "  have hsnoc : ∀ {a b c : α}, StarStep (Conv R) a b → Conv R b c → StarStep (Conv R) a c := by\n"
                "    intro a b c hab hbc\n"
                "    induction hab with\n"
                "    | refl _ => exact StarStep.step hbc (StarStep.refl _)\n"
                "    | step hr _ ih => exact StarStep.step hr (ih hbc)\n"
                "  induction h with\n"
                "  | refl a => exact StarStep.refl a\n"
                "  | step hr _ ih => exact hsnoc ih hr"
            ),
        },
        {
            "id": "eval_07_classical_imp_iff_or",
            "domain": "logic_functions",
            "title": "Material Implication Equivalence (P → Q) ↔ (¬P ∨ Q)",
            "preamble": "",
            "theorem_header": "theorem imp_iff_not_or_classical (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) :=",
            "reference_sketchpad": "Forward direction splits on `Classical.em P`; backward direction destructs `¬ P ∨ Q` constructively.",
            "reference_proof": (
                "by\n"
                "  constructor\n"
                "  · intro h\n"
                "    cases Classical.em P with\n"
                "    | inl hp => exact Or.inr (h hp)\n"
                "    | inr hnp => exact Or.inl hnp\n"
                "  · rintro (hnp | hq) hp\n"
                "    · exact False.elim (hnp hp)\n"
                "    · exact hq"
            ),
        },
        {
            "id": "eval_08_iter_periodic",
            "domain": "logic_functions",
            "title": "Periodic Point Invariance Under Multiples of the Period",
            "preamble": (
                "def iterFn {α : Type} (f : α → α) : Nat → α → α\n"
                "  | 0, x => x\n"
                "  | n + 1, x => f (iterFn f n x)"
            ),
            "theorem_header": (
                "theorem iterFn_mul_period {α : Type} (f : α → α) (p : Nat) (x : α) "
                "(hp : iterFn f p x = x) (k : Nat) : iterFn f (p * k) x = x :="
            ),
            "reference_sketchpad": "First prove `hadd : ∀ a b y, iterFn f (a + b) y = iterFn f a (iterFn f b y)`. Then induct on `k`, rewriting `p * (k + 1) = p * k + p` or `p + p * k` (`Nat.mul_succ` + `Nat.add_comm`).",
            "reference_proof": (
                "by\n"
                "  have hadd : ∀ (a b : Nat) (y : α), iterFn f (a + b) y = iterFn f a (iterFn f b y) := by\n"
                "    intro a b y\n"
                "    induction a with\n"
                "    | zero => simp [iterFn]\n"
                "    | succ m ih => rw [Nat.succ_add, iterFn, iterFn, ih]\n"
                "  induction k with\n"
                "  | zero => simp [iterFn]\n"
                "  | succ m ih =>\n"
                "    rw [Nat.mul_succ, hadd, hp, ih]"
            ),
        },
        {
            "id": "eval_09_lenAcc_correct",
            "domain": "inductive_ds",
            "title": "Tail-Recursive List Length Accumulator",
            "preamble": (
                "def lenAcc {α : Type} : List α → Nat → Nat\n"
                "  | [], acc => acc\n"
                "  | _ :: xs, acc => lenAcc xs (acc + 1)"
            ),
            "theorem_header": (
                "theorem lenAcc_zero_eq_length {α : Type} (xs : List α) : lenAcc xs 0 = xs.length :="
            ),
            "reference_sketchpad": "Prove `haux : ∀ (ys : List α) (acc : Nat), lenAcc ys acc = acc + ys.length` by `induction ys generalizing acc` and `omega`, then specialize at `0`.",
            "reference_proof": (
                "by\n"
                "  have haux : ∀ (ys : List α) (acc : Nat), lenAcc ys acc = acc + ys.length := by\n"
                "    intro ys\n"
                "    induction ys with\n"
                "    | nil => intro acc; simp [lenAcc]\n"
                "    | cons _ tl ih => intro acc; simp [lenAcc, ih (acc + 1)]; omega\n"
                "  simpa using haux xs 0"
            ),
        },
        {
            "id": "eval_10_btree_leaves_pos",
            "domain": "inductive_ds",
            "title": "Leaf Count vs Node Count on Binary Trees",
            "preamble": (
                "inductive BTree (α : Type) where\n"
                "  | leaf : BTree α\n"
                "  | node : BTree α → α → BTree α → BTree α\n\n"
                "def countLeaves {α : Type} : BTree α → Nat\n"
                "  | BTree.leaf => 1\n"
                "  | BTree.node l _ r => countLeaves l + countLeaves r\n\n"
                "def countNodes {α : Type} : BTree α → Nat\n"
                "  | BTree.leaf => 0\n"
                "  | BTree.node l _ r => 1 + countNodes l + countNodes r"
            ),
            "theorem_header": (
                "theorem btree_leaves_eq_nodes_succ {α : Type} (t : BTree α) : "
                "countLeaves t = countNodes t + 1 :="
            ),
            "reference_sketchpad": "Induct on `t : BTree α`; `leaf` is `1 = 0 + 1`, and `node` follows from `ihl`, `ihr`, and `omega`.",
            "reference_proof": (
                "by\n"
                "  induction t with\n"
                "  | leaf => rfl\n"
                "  | node l _ r ihl ihr => simp [countLeaves, countNodes, ihl, ihr]; omega"
            ),
        },
        {
            "id": "eval_11_dvd_diff_nat",
            "domain": "nat_number_theory",
            "title": "Divisibility of Integer Linear Combination",
            "preamble": "def IntDvd (d n : Int) : Prop := ∃ k : Int, n = d * k",
            "theorem_header": (
                "theorem int_dvd_sub_comb (d a b x y : Int) "
                "(ha : IntDvd d a) (hb : IntDvd d b) : IntDvd d (a * x - b * y) :="
            ),
            "reference_sketchpad": "Unpack `⟨ka, rfl⟩` and `⟨kb, rfl⟩`, choose witness `ka * x - kb * y`, and rewrite with `Int.mul_sub` and `Int.mul_assoc`.",
            "reference_proof": (
                "by\n"
                "  rcases ha with ⟨ka, rfl⟩\n"
                "  rcases hb with ⟨kb, rfl⟩\n"
                "  refine ⟨ka * x - kb * y, ?_⟩\n"
                "  rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc]"
            ),
        },
        {
            "id": "eval_12_sum_squares_six",
            "domain": "nat_number_theory",
            "title": "Sum of First n Squares Formula 6 * Σ k^2 = n(n+1)(2n+1)",
            "preamble": (
                "def sumSq : Nat → Nat\n"
                "  | 0 => 0\n"
                "  | n + 1 => sumSq n + (n + 1) * (n + 1)"
            ),
            "theorem_header": (
                "theorem sum_squares_six (n : Nat) : "
                "6 * sumSq n = n * (n + 1) * (2 * n + 1) :="
            ),
            "reference_sketchpad": "Induct on `n`. In `succ k ih`, factor `(k + 1)` out of both sides or expand products into `k^3`, `k^2`, `k`, and `1` via `Nat.left_distrib`/`Nat.right_distrib` and close with `omega`.",
            "reference_proof": (
                "by\n"
                "  induction n with\n"
                "  | zero => rfl\n"
                "  | succ k ih =>\n"
                "    rw [sumSq, Nat.left_distrib, ih]\n"
                "    have h1 : k * (k + 1) * (2 * k + 1) = (k * (2 * k + 1)) * (k + 1) := by\n"
                "      rw [Nat.mul_assoc, Nat.mul_comm (k + 1) (2 * k + 1), ← Nat.mul_assoc]\n"
                "    have h2 : 6 * ((k + 1) * (k + 1)) = (6 * (k + 1)) * (k + 1) := by\n"
                "      rw [← Nat.mul_assoc]\n"
                "    have h3 : (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) = ((k + 2) * (2 * k + 3)) * (k + 1) := by\n"
                "      have ha : k + 1 + 1 = k + 2 := rfl\n"
                "      have hb : 2 * (k + 1) + 1 = 2 * k + 3 := by omega\n"
                "      rw [ha, hb, Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, Nat.mul_comm (k + 1) (2 * k + 3), ← Nat.mul_assoc]\n"
                "    have h4 : k * (2 * k + 1) + 6 * (k + 1) = (k + 2) * (2 * k + 3) := by\n"
                "      rw [Nat.left_distrib k (2 * k) 1, Nat.right_distrib k 2 (2 * k + 3), Nat.left_distrib k (2 * k) 3]\n"
                "      omega\n"
                "    rw [h1, h2, h3, ← Nat.right_distrib, h4]"
            ),
        },
    ]


def generate_and_verify_benchmarks(
    grpo_path: str = "data/stage3_hard_grpo.jsonl",
    eval_path: str = "data/eval_holdout.jsonl",
) -> Dict:
    grpo_qs = build_hard_grpo_questions()
    eval_qs = build_eval_holdout_questions()

    for label, qs in [("Stage3_Hard_GRPO", grpo_qs), ("Eval_Holdout", eval_qs)]:
        for q in qs:
            resp = build_assistant_sketchpad_response(q["reference_sketchpad"], q["reference_proof"])
            res = verify_single_proof(q["preamble"], q["theorem_header"], resp)
            if not res.verified_correct:
                raise RuntimeError(
                    f"[{label}] Reference proof FAILED Lean 4.36 verification for {q['id']}: "
                    f"{res.error_summary} (axioms={res.axioms_used})"
                )
            q["verified_axioms"] = res.axioms_used

    os.makedirs(os.path.dirname(grpo_path), exist_ok=True)
    with open(grpo_path, "w", encoding="utf-8") as f:
        for q in grpo_qs:
            f.write(json.dumps(q, ensure_ascii=False) + "\n")

    with open(eval_path, "w", encoding="utf-8") as f:
        for q in eval_qs:
            f.write(json.dumps(q, ensure_ascii=False) + "\n")

    summary = {
        "stage3_hard_grpo_count": len(grpo_qs),
        "eval_holdout_count": len(eval_qs),
        "all_kernel_verified": True,
        "grpo_ids": [q["id"] for q in grpo_qs],
        "eval_ids": [q["id"] for q in eval_qs],
    }
    print("Benchmark Verification Summary:", json.dumps(summary, indent=2))
    return summary


if __name__ == "__main__":
    generate_and_verify_benchmarks()
