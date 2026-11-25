/-!
# Unseen Holdout Pure Lean 4 Evaluation Suite (12 Problems)

Zero-Mathlib pure Lean 4.36 formalizations verified by the Lean kernel.
-/

/-! ## 1. Uniqueness of Two-Sided Monoid Identity (`algebra`) -/
namespace eval_01_unique_identity

class PureMonoid (M : Type) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

theorem unique_left_id {M : Type} [PureMonoid M] (e : M) (he : ∀ x : M, PureMonoid.mul e x = x) : e = PureMonoid.one :=
by
  have h := he PureMonoid.one
  rw [PureMonoid.mul_one] at h
  exact h

#print axioms unique_left_id

end eval_01_unique_identity

/-! ## 2. Uniqueness of Right Inverse in a Group (`algebra`) -/
namespace eval_02_group_unique_inv

class PureGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

theorem unique_right_inv {G : Type} [PureGroup G] (a b : G) (h : PureGroup.mul a b = PureGroup.one) : b = PureGroup.inv a :=
by
  have h1 := congrArg (PureGroup.mul (PureGroup.inv a)) h
  rw [← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.mul_one] at h1
  exact h1

#print axioms unique_right_inv

end eval_02_group_unique_inv

/-! ## 3. Associativity of Join in a Pure Lattice (`order_lattice`) -/
namespace eval_03_lattice_sup_assoc

class PureLattice (L : Type) where
  le : L → L → Prop
  sup : L → L → L
  inf : L → L → L
  le_refl : ∀ a : L, le a a
  le_trans : ∀ {a b c : L}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b
  le_sup_left : ∀ a b : L, le a (sup a b)
  le_sup_right : ∀ a b : L, le b (sup a b)
  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c

theorem sup_assoc_pure {L : Type} [PureLattice L] (a b c : L) : PureLattice.sup (PureLattice.sup a b) c = PureLattice.sup a (PureLattice.sup b c) :=
by
  apply PureLattice.le_antisymm
  · apply PureLattice.sup_le
    · apply PureLattice.sup_le (PureLattice.le_sup_left _ _)
      exact PureLattice.le_trans (PureLattice.le_sup_left b c) (PureLattice.le_sup_right a _)
    · exact PureLattice.le_trans (PureLattice.le_sup_right b c) (PureLattice.le_sup_right a _)
  · apply PureLattice.sup_le
    · exact PureLattice.le_trans (PureLattice.le_sup_left a b) (PureLattice.le_sup_left _ c)
    · apply PureLattice.sup_le
      · exact PureLattice.le_trans (PureLattice.le_sup_right a b) (PureLattice.le_sup_left _ c)
      · exact PureLattice.le_sup_right _ c

#print axioms sup_assoc_pure

end eval_03_lattice_sup_assoc

/-! ## 4. Meet of Two Closure-Fixed Elements Is Fixed (`order_lattice`) -/
namespace eval_04_closure_inf_closed

class PureLattice (L : Type) where
  le : L → L → Prop
  inf : L → L → L
  le_refl : ∀ a : L, le a a
  le_trans : ∀ {a b c : L}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : L}, le a b → le b a → a = b
  inf_le_left : ∀ a b : L, le (inf a b) a
  inf_le_right : ∀ a b : L, le (inf a b) b
  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)

structure ClosureOp (L : Type) [PureLattice L] (cl : L → L) : Prop where
  extensive : ∀ x, PureLattice.le x (cl x)
  monotone : ∀ {x y}, PureLattice.le x y → PureLattice.le (cl x) (cl y)
  idempotent : ∀ x, cl (cl x) = cl x

theorem closed_inf_closed {L : Type} [PureLattice L] (cl : L → L) (hcl : ClosureOp L cl) (a b : L) (ha : cl a = a) (hb : cl b = b) : cl (PureLattice.inf a b) = PureLattice.inf a b :=
by
  apply PureLattice.le_antisymm
  · apply PureLattice.le_inf
    · have h1 := hcl.monotone (PureLattice.inf_le_left a b)
      rw [ha] at h1; exact h1
    · have h2 := hcl.monotone (PureLattice.inf_le_right a b)
      rw [hb] at h2; exact h2
  · exact hcl.extensive _

#print axioms closed_inf_closed

end eval_04_closure_inf_closed

/-! ## 5. Preimage Commutes with Set Complement (`relations_sets`) -/
namespace eval_05_preimg_compl

def SetP (α : Type) := α → Prop
def ComplP {α : Type} (S : SetP α) : SetP α := fun x => ¬ S x
def PreimgP {α β : Type} (f : α → β) (T : SetP β) : SetP α := fun x => T (f x)

theorem preimg_compl_eq {α β : Type} (f : α → β) (T : SetP β) : PreimgP f (ComplP T) = ComplP (PreimgP f T) :=
by
  rfl

#print axioms preimg_compl_eq

end eval_05_preimg_compl

/-! ## 6. Converse Commutes with Reflexive-Transitive Closure (`relations_sets`) -/
namespace eval_06_star_reverse_ind

inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : StarStep R x x
  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z

def Conv (R : α → α → Prop) : α → α → Prop := fun x y => R y x

theorem star_conv_imp {α : Type} (R : α → α → Prop) {x y : α} (h : StarStep R x y) : StarStep (Conv R) y x :=
by
  have hsnoc : ∀ {a b c : α}, StarStep (Conv R) a b → Conv R b c → StarStep (Conv R) a c := by
    intro a b c hab hbc
    induction hab with
    | refl _ => exact StarStep.step hbc (StarStep.refl _)
    | step hr _ ih => exact StarStep.step hr (ih hbc)
  induction h with
  | refl a => exact StarStep.refl a
  | step hr _ ih => exact hsnoc ih hr

#print axioms star_conv_imp

end eval_06_star_reverse_ind

/-! ## 7. Material Implication Equivalence (P → Q) ↔ (¬P ∨ Q) (`logic_functions`) -/
namespace eval_07_classical_imp_iff_or

theorem imp_iff_not_or_classical (P Q : Prop) : (P → Q) ↔ (¬ P ∨ Q) :=
by
  constructor
  · intro h
    cases Classical.em P with
    | inl hp => exact Or.inr (h hp)
    | inr hnp => exact Or.inl hnp
  · rintro (hnp | hq) hp
    · exact False.elim (hnp hp)
    · exact hq

#print axioms imp_iff_not_or_classical

end eval_07_classical_imp_iff_or

/-! ## 8. Periodic Point Invariance Under Multiples of the Period (`logic_functions`) -/
namespace eval_08_iter_periodic

def iterFn {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterFn f n x)

theorem iterFn_mul_period {α : Type} (f : α → α) (p : Nat) (x : α) (hp : iterFn f p x = x) (k : Nat) : iterFn f (p * k) x = x :=
by
  have hadd : ∀ (a b : Nat) (y : α), iterFn f (a + b) y = iterFn f a (iterFn f b y) := by
    intro a b y
    induction a with
    | zero => simp [iterFn]
    | succ m ih => rw [Nat.succ_add, iterFn, iterFn, ih]
  induction k with
  | zero => simp [iterFn]
  | succ m ih =>
    rw [Nat.mul_succ, hadd, hp, ih]

#print axioms iterFn_mul_period

end eval_08_iter_periodic

/-! ## 9. Tail-Recursive List Length Accumulator (`inductive_ds`) -/
namespace eval_09_lenAcc_correct

def lenAcc {α : Type} : List α → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => lenAcc xs (acc + 1)

theorem lenAcc_zero_eq_length {α : Type} (xs : List α) : lenAcc xs 0 = xs.length :=
by
  have haux : ∀ (ys : List α) (acc : Nat), lenAcc ys acc = acc + ys.length := by
    intro ys
    induction ys with
    | nil => intro acc; simp [lenAcc]
    | cons _ tl ih => intro acc; simp [lenAcc, ih (acc + 1)]; omega
  simpa using haux xs 0

#print axioms lenAcc_zero_eq_length

end eval_09_lenAcc_correct

/-! ## 10. Leaf Count vs Node Count on Binary Trees (`inductive_ds`) -/
namespace eval_10_btree_leaves_pos

inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α

def countLeaves {α : Type} : BTree α → Nat
  | BTree.leaf => 1
  | BTree.node l _ r => countLeaves l + countLeaves r

def countNodes {α : Type} : BTree α → Nat
  | BTree.leaf => 0
  | BTree.node l _ r => 1 + countNodes l + countNodes r

theorem btree_leaves_eq_nodes_succ {α : Type} (t : BTree α) : countLeaves t = countNodes t + 1 :=
by
  induction t with
  | leaf => rfl
  | node l _ r ihl ihr => simp [countLeaves, countNodes, ihl, ihr]; omega

#print axioms btree_leaves_eq_nodes_succ

end eval_10_btree_leaves_pos

/-! ## 11. Divisibility of Integer Linear Combination (`nat_number_theory`) -/
namespace eval_11_dvd_diff_nat

def IntDvd (d n : Int) : Prop := ∃ k : Int, n = d * k

theorem int_dvd_sub_comb (d a b x y : Int) (ha : IntDvd d a) (hb : IntDvd d b) : IntDvd d (a * x - b * y) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨ka * x - kb * y, ?_⟩
  rw [Int.mul_sub, ← Int.mul_assoc, ← Int.mul_assoc]

#print axioms int_dvd_sub_comb

end eval_11_dvd_diff_nat

/-! ## 12. Sum of First n Squares Formula 6 * Σ k^2 = n(n+1)(2n+1) (`nat_number_theory`) -/
namespace eval_12_sum_squares_six

def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) * (n + 1)

theorem sum_squares_six (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) :=
by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumSq, Nat.left_distrib, ih]
    have h1 : k * (k + 1) * (2 * k + 1) = (k * (2 * k + 1)) * (k + 1) := by
      rw [Nat.mul_assoc, Nat.mul_comm (k + 1) (2 * k + 1), ← Nat.mul_assoc]
    have h2 : 6 * ((k + 1) * (k + 1)) = (6 * (k + 1)) * (k + 1) := by
      rw [← Nat.mul_assoc]
    have h3 : (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1) = ((k + 2) * (2 * k + 3)) * (k + 1) := by
      have ha : k + 1 + 1 = k + 2 := rfl
      have hb : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [ha, hb, Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, Nat.mul_comm (k + 1) (2 * k + 3), ← Nat.mul_assoc]
    have h4 : k * (2 * k + 1) + 6 * (k + 1) = (k + 2) * (2 * k + 3) := by
      rw [Nat.left_distrib k (2 * k) 1, Nat.right_distrib k 2 (2 * k + 3), Nat.left_distrib k (2 * k) 3]
      omega
    rw [h1, h2, h3, ← Nat.right_distrib, h4]

#print axioms sum_squares_six

end eval_12_sum_squares_six
