/-!
# Stage 3 Hard Multi-Step Pure Lean 4 Theorems (15 Problems)

Zero-Mathlib pure Lean 4.36 formalizations verified by the Lean kernel.
-/

/-! ## 1. Groups of Exponent 2 Are Abelian (`algebra`) -/
namespace hq_01_exp2_group_comm

class PureGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

theorem exp2_group_abelian {G : Type} [PureGroup G] (hexp : ∀ x : G, PureGroup.mul x x = PureGroup.one) (a b : G) : PureGroup.mul a b = PureGroup.mul b a :=
by
  have h1 : PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a) = PureGroup.one := by
    calc PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a)
      _ = PureGroup.mul a (PureGroup.mul b (PureGroup.mul b a)) := by rw [PureGroup.mul_assoc]
      _ = PureGroup.mul a (PureGroup.mul (PureGroup.mul b b) a) := by rw [← PureGroup.mul_assoc b b a]
      _ = PureGroup.one := by rw [hexp b, PureGroup.one_mul, hexp a]
  have h2 : PureGroup.mul (PureGroup.mul a b) (PureGroup.mul a b) = PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a) := by
    rw [hexp (PureGroup.mul a b), h1]
  calc PureGroup.mul a b
    _ = PureGroup.mul PureGroup.one (PureGroup.mul a b) := by rw [PureGroup.one_mul]
    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul a b)) (PureGroup.mul a b) := by rw [PureGroup.inv_mul]
    _ = PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul (PureGroup.mul a b) (PureGroup.mul a b)) := by rw [PureGroup.mul_assoc]
    _ = PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul (PureGroup.mul a b) (PureGroup.mul b a)) := by rw [h2]
    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.mul a b)) (PureGroup.mul a b)) (PureGroup.mul b a) := by rw [← PureGroup.mul_assoc]
    _ = PureGroup.mul b a := by rw [PureGroup.inv_mul, PureGroup.one_mul]

#print axioms exp2_group_abelian

end hq_01_exp2_group_comm

/-! ## 2. Upper Adjoint Stabilization u(l(u(b))) = u(b) (`order_lattice`) -/
namespace hq_02_galois_u_l_u

class PurePoset (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

structure GaloisConn (A B : Type) [PurePoset A] [PurePoset B] (l : A → B) (u : B → A) : Prop where
  adj : ∀ a b, PurePoset.le (l a) b ↔ PurePoset.le a (u b)

theorem galois_u_l_u {A B : Type} [PurePoset A] [PurePoset B] (l : A → B) (u : B → A) (hgc : GaloisConn A B l u) (b : B) : u (l (u b)) = u b :=
by
  apply PurePoset.le_antisymm
  · have hc1 : PurePoset.le (l (u (l (u b)))) (l (u b)) := (hgc.adj (u (l (u b))) (l (u b))).mpr (PurePoset.le_refl _)
    have hc2 : PurePoset.le (l (u b)) b := (hgc.adj (u b) b).mpr (PurePoset.le_refl _)
    exact (hgc.adj (u (l (u b))) b).mp (PurePoset.le_trans hc1 hc2)
  · exact (hgc.adj (u b) (l (u b))).mp (PurePoset.le_refl _)

#print axioms galois_u_l_u

end hq_02_galois_u_l_u

/-! ## 3. Classical Quantifier Distribution (∀ x, P ∨ Q x) → P ∨ (∀ x, Q x) (`logic_functions`) -/
namespace hq_03_classical_forall_or

theorem forall_or_distrib_left {α : Type} (P : Prop) (Q : α → Prop) : (∀ x : α, P ∨ Q x) → P ∨ (∀ x : α, Q x) :=
by
  intro h
  cases Classical.em P with
  | inl hp => exact Or.inl hp
  | inr hnp =>
    apply Or.inr
    intro x
    rcases h x with hp | hqx
    · exact False.elim (hnp hp)
    · exact hqx

#print axioms forall_or_distrib_left

end hq_03_classical_forall_or

/-! ## 4. Inorder Flatten of Mirrored Binary Tree Reverses List (`inductive_ds`) -/
namespace hq_04_btree_flatten_mirror

inductive BTree (α : Type) where
  | leaf : BTree α
  | node : BTree α → α → BTree α → BTree α

def mirrorT {α : Type} : BTree α → BTree α
  | BTree.leaf => BTree.leaf
  | BTree.node l v r => BTree.node (mirrorT r) v (mirrorT l)

def flattenBT {α : Type} : BTree α → List α
  | BTree.leaf => []
  | BTree.node l v r => flattenBT l ++ [v] ++ flattenBT r

theorem flattenBT_mirrorT {α : Type} (t : BTree α) : flattenBT (mirrorT t) = (flattenBT t).reverse :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp [mirrorT, flattenBT, ihl, ihr, List.reverse_append, List.append_assoc]

#print axioms flattenBT_mirrorT

end hq_04_btree_flatten_mirror

/-! ## 5. Injective Left-Inverse Is Also a Two-Sided Inverse (`logic_functions`) -/
namespace hq_05_retraction_inj_right_inv

def InjFn {α β : Type} (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y
def SurjFn {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y
def LeftInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ x : α, g (f x) = x
def RightInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ y : β, f (g y) = y

theorem right_inv_and_surj_of_left_inv_inj {α β : Type} (f : α → β) (g : β → α) (hleft : LeftInvFn g f) (hinjg : InjFn g) : RightInvFn g f ∧ SurjFn f :=
by
  have hr : RightInvFn g f := by
    intro y
    exact hinjg (hleft (g y))
  exact ⟨hr, fun y => ⟨g y, hr y⟩⟩

#print axioms right_inv_and_surj_of_left_inv_inj

end hq_05_retraction_inj_right_inv

/-! ## 6. Tail-Recursive Map Accumulator Equivalence (`inductive_ds`) -/
namespace hq_06_mapAcc_correct

def mapAcc {α β : Type} (f : α → β) : List α → List β → List β
  | [], acc => acc.reverse
  | x :: xs, acc => mapAcc f xs (f x :: acc)

theorem mapAcc_nil_eq_map {α β : Type} (f : α → β) (xs : List α) : mapAcc f xs [] = List.map f xs :=
by
  have haux : ∀ (ys : List α) (acc : List β), mapAcc f ys acc = acc.reverse ++ List.map f ys := by
    intro ys
    induction ys with
    | nil => intro acc; simp [mapAcc]
    | cons y tl ih =>
      intro acc
      simp [mapAcc, ih (f y :: acc), List.append_assoc]
  simpa using haux xs []

#print axioms mapAcc_nil_eq_map

end hq_06_mapAcc_correct

/-! ## 7. Heyting Algebra Residuation Currying (a ⊓ b) ⇨ c = a ⇨ (b ⇨ c) (`order_lattice`) -/
namespace hq_07_heyting_curry

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
  le_himp_iff : ∀ a b c : H, BoundedLattice.le a (himp b c) ↔ BoundedLattice.le (BoundedLattice.inf a b) c

theorem heyting_curry {H : Type} [HeytingAlg H] (a b c : H) : HeytingAlg.himp (BoundedLattice.inf a b) c = HeytingAlg.himp a (HeytingAlg.himp b c) :=
by
  apply BoundedLattice.le_antisymm
  · apply (HeytingAlg.le_himp_iff _ a _).mpr
    apply (HeytingAlg.le_himp_iff _ b c).mpr
    have hassoc1 : BoundedLattice.le (BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) a) b) (BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) (BoundedLattice.inf a b)) := by
      apply BoundedLattice.le_inf
      · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_left _ _)
      · apply BoundedLattice.le_inf
        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_right _ _)
        · exact BoundedLattice.inf_le_right _ _
    have hmp : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp (BoundedLattice.inf a b) c) (BoundedLattice.inf a b)) c := (HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)
    exact BoundedLattice.le_trans hassoc1 hmp
  · apply (HeytingAlg.le_himp_iff _ (BoundedLattice.inf a b) c).mpr
    have hmp1 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) a) (HeytingAlg.himp b c) := (HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)
    have hstep : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) (BoundedLattice.inf a b)) (BoundedLattice.inf (HeytingAlg.himp b c) b) := by
      apply BoundedLattice.le_inf
      · have hl : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) (BoundedLattice.inf a b)) (BoundedLattice.inf (HeytingAlg.himp a (HeytingAlg.himp b c)) a) := by
          apply BoundedLattice.le_inf (BoundedLattice.inf_le_left _ _)
          exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) (BoundedLattice.inf_le_left _ _)
        exact BoundedLattice.le_trans hl hmp1
      · exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) (BoundedLattice.inf_le_right _ _)
    have hmp2 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp b c) b) c := (HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)
    exact BoundedLattice.le_trans hstep hmp2

#print axioms heyting_curry

end hq_07_heyting_curry

/-! ## 8. Church-Rosser Diamond Strip Lemma (`relations_sets`) -/
namespace hq_08_diamond_strip_lemma

inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : StarStep R x x
  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z

def Diamond {α : Type} (R : α → α → Prop) : Prop :=
  ∀ {x y z : α}, R x y → R x z → ∃ w : α, R y w ∧ R z w

theorem diamond_strip {α : Type} (R : α → α → Prop) (hdiam : Diamond R) {x y z : α} (hxy : R x y) (hxz : StarStep R x z) : ∃ w : α, StarStep R y w ∧ R z w :=
by
  induction hxz generalizing y with
  | refl _ => exact ⟨y, StarStep.refl y, hxy⟩
  | step hxu _ ih =>
    rcases hdiam hxy hxu with ⟨v, hyv, huv⟩
    rcases ih huv with ⟨w, hvw, hzw⟩
    exact ⟨w, StarStep.step hyv hvw, hzw⟩

#print axioms diamond_strip

end hq_08_diamond_strip_lemma

/-! ## 9. Divisibility of n^3 + 2n by 3 (`nat_number_theory`) -/
namespace hq_09_div3_cube_plus_2n

def PureDvd (d n : Nat) : Prop := ∃ k : Nat, n = d * k

theorem dvd3_cube_add_two_mul (n : Nat) : PureDvd 3 (n * n * n + 2 * n) :=
by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨m, hm⟩
    refine ⟨m + (k * k + k + 1), ?_⟩
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]
      omega
    have hcb : (k + 1) * (k + 1) * (k + 1) = k * k * k + 3 * (k * k) + 3 * k + 1 := by
      rw [hsq, Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]
      rw [Nat.mul_assoc 2 k k]
      omega
    omega

#print axioms dvd3_cube_add_two_mul

end hq_09_div3_cube_plus_2n

/-! ## 10. Product of Two Negatives in a Ring: (-a) * (-b) = a * b (`algebra`) -/
namespace hq_10_ring_neg_mul_neg

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
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

theorem ring_neg_mul_neg {R : Type} [PureRing R] (a b : R) : PureRing.mul (PureRing.neg a) (PureRing.neg b) = PureRing.mul a b :=
by
  have hz_r : PureRing.mul (PureRing.neg a) PureRing.zero = PureRing.zero := by
    have h0 : PureRing.add (PureRing.mul (PureRing.neg a) PureRing.zero) (PureRing.mul (PureRing.neg a) PureRing.zero) = PureRing.add (PureRing.mul (PureRing.neg a) PureRing.zero) PureRing.zero := by
      rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]
    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul (PureRing.neg a) PureRing.zero))) h0
    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'
    exact h0'
  have hz_l : PureRing.mul PureRing.zero b = PureRing.zero := by
    have h0 : PureRing.add (PureRing.mul PureRing.zero b) (PureRing.mul PureRing.zero b) = PureRing.add (PureRing.mul PureRing.zero b) PureRing.zero := by
      rw [← PureRing.right_distrib, PureRing.zero_add, PureRing.add_zero]
    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul PureRing.zero b))) h0
    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'
    exact h0'
  have heq : PureRing.add (PureRing.mul (PureRing.neg a) b) (PureRing.mul (PureRing.neg a) (PureRing.neg b)) = PureRing.add (PureRing.mul (PureRing.neg a) b) (PureRing.mul a b) := by
    rw [← PureRing.left_distrib, PureRing.add_neg, hz_r, ← PureRing.right_distrib, PureRing.neg_add, hz_l]
  have hfin := congrArg (PureRing.add (PureRing.neg (PureRing.mul (PureRing.neg a) b))) heq
  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at hfin
  exact hfin

#print axioms ring_neg_mul_neg

end hq_10_ring_neg_mul_neg

/-! ## 11. Continuation-Passing Expressibility of foldl via foldr (`inductive_ds`) -/
namespace hq_11_foldl_via_foldr_cps

def foldrL {α β : Type} (f : α → β → β) (z : β) : List α → β
  | [] => z
  | x :: xs => f x (foldrL f z xs)

def foldlL {α β : Type} (f : β → α → β) : β → List α → β
  | acc, [] => acc
  | acc, x :: xs => foldlL f (f acc x) xs

theorem foldl_eq_foldr_cps {α β : Type} (f : β → α → β) (xs : List α) (acc : β) : foldrL (fun x k a => k (f a x)) (fun a => a) xs acc = foldlL f acc xs :=
by
  induction xs generalizing acc with
  | nil => rfl
  | cons x tl ih =>
    simp only [foldrL, foldlL]
    exact ih (f acc x)

#print axioms foldl_eq_foldr_cps

end hq_11_foldl_via_foldr_cps

/-! ## 12. Inverse of a Group Commutator [a, b]⁻¹ = [b, a] (`algebra`) -/
namespace hq_12_group_commutator_inv

class PureGroup (G : Type) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul : ∀ a : G, mul (inv a) a = one
  mul_inv : ∀ a : G, mul a (inv a) = one

def commG {G : Type} [PureGroup G] (a b : G) : G :=
  PureGroup.mul (PureGroup.mul (PureGroup.mul a b) (PureGroup.inv a)) (PureGroup.inv b)

theorem commG_inv {G : Type} [PureGroup G] (a b : G) : PureGroup.inv (commG a b) = commG b a :=
by
  have cancel_mid : ∀ x y z : G, PureGroup.mul (PureGroup.mul x y) (PureGroup.mul (PureGroup.inv y) z) = PureGroup.mul x z := by
    intro x y z
    rw [PureGroup.mul_assoc x y (PureGroup.mul (PureGroup.inv y) z)]
    rw [← PureGroup.mul_assoc y (PureGroup.inv y) z, PureGroup.mul_inv, PureGroup.one_mul]
  have cancel_mid_inv : ∀ x y z : G, PureGroup.mul (PureGroup.mul x (PureGroup.inv y)) (PureGroup.mul y z) = PureGroup.mul x z := by
    intro x y z
    rw [PureGroup.mul_assoc x (PureGroup.inv y) (PureGroup.mul y z)]
    rw [← PureGroup.mul_assoc (PureGroup.inv y) y z, PureGroup.inv_mul, PureGroup.one_mul]
  have hprod : PureGroup.mul (commG a b) (commG b a) = PureGroup.one := by
    unfold commG
    have s1 : PureGroup.mul (PureGroup.mul (PureGroup.mul b a) (PureGroup.inv b)) (PureGroup.inv a) = PureGroup.mul b (PureGroup.mul a (PureGroup.mul (PureGroup.inv b) (PureGroup.inv a))) := by
      rw [PureGroup.mul_assoc, PureGroup.mul_assoc]
    rw [s1, cancel_mid_inv, cancel_mid_inv, cancel_mid, PureGroup.mul_inv]
  calc PureGroup.inv (commG a b)
    _ = PureGroup.mul (PureGroup.inv (commG a b)) PureGroup.one := by rw [PureGroup.mul_one]
    _ = PureGroup.mul (PureGroup.inv (commG a b)) (PureGroup.mul (commG a b) (commG b a)) := by rw [hprod]
    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (commG a b)) (commG a b)) (commG b a) := by rw [← PureGroup.mul_assoc]
    _ = commG b a := by rw [PureGroup.inv_mul, PureGroup.one_mul]

#print axioms commG_inv

end hq_12_group_commutator_inv

/-! ## 13. Fibonacci Addition Identity F_{m+n+1} = F_m F_n + F_{m+1} F_{n+1} (`nat_number_theory`) -/
namespace hq_13_fib_addition_formula

def fibN : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fibN n + fibN (n + 1)

theorem fibN_add_succ (m n : Nat) : fibN (m + n + 1) = fibN m * fibN n + fibN (m + 1) * fibN (n + 1) :=
by
  induction n generalizing m with
  | zero => simp [fibN]
  | succ k ih =>
    have hshift : m + (k + 1) + 1 = (m + 1) + k + 1 := by omega
    rw [hshift, ih (m + 1)]
    have hm2 : fibN (m + 1 + 1) = fibN m + fibN (m + 1) := rfl
    have hk2 : fibN (k + 1 + 1) = fibN k + fibN (k + 1) := rfl
    rw [hm2, hk2, Nat.right_distrib, Nat.left_distrib]
    omega

#print axioms fibN_add_succ

end hq_13_fib_addition_formula

/-! ## 14. Stack Virtual Machine Compiler Correctness for Add + Mul AST (`inductive_ds`) -/
namespace hq_14_arith_vm_compiler

inductive ArithAST where
  | lit : Nat → ArithAST
  | add : ArithAST → ArithAST → ArithAST
  | mul : ArithAST → ArithAST → ArithAST

def evalAST : ArithAST → Nat
  | ArithAST.lit n => n
  | ArithAST.add e1 e2 => evalAST e1 + evalAST e2
  | ArithAST.mul e1 e2 => evalAST e1 * evalAST e2

inductive OpInstr where
  | push : Nat → OpInstr
  | addOp : OpInstr
  | mulOp : OpInstr

def execOps : List OpInstr → List Nat → List Nat
  | [], stk => stk
  | OpInstr.push n :: ops, stk => execOps ops (n :: stk)
  | OpInstr.addOp :: ops, b :: a :: stk => execOps ops ((a + b) :: stk)
  | OpInstr.addOp :: ops, stk => execOps ops stk
  | OpInstr.mulOp :: ops, b :: a :: stk => execOps ops ((a * b) :: stk)
  | OpInstr.mulOp :: ops, stk => execOps ops stk

def compileAST : ArithAST → List OpInstr
  | ArithAST.lit n => [OpInstr.push n]
  | ArithAST.add e1 e2 => compileAST e1 ++ compileAST e2 ++ [OpInstr.addOp]
  | ArithAST.mul e1 e2 => compileAST e1 ++ compileAST e2 ++ [OpInstr.mulOp]

theorem compileAST_correct (e : ArithAST) (stk : List Nat) : execOps (compileAST e) stk = evalAST e :: stk :=
by
  have hexec : ∀ (c1 c2 : List OpInstr) (s : List Nat), execOps (c1 ++ c2) s = execOps c2 (execOps c1 s) := by
    intro c1 c2
    induction c1 with
    | nil => intro s; rfl
    | cons op rest ih =>
      intro s
      cases op with
      | push n => exact ih (n :: s)
      | addOp =>
        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩
        · exact ih []
        · exact ih [b]
        · exact ih ((a + b) :: s')
      | mulOp =>
        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩
        · exact ih []
        · exact ih [b]
        · exact ih ((a * b) :: s')
  induction e generalizing stk with
  | lit n => rfl
  | add e1 e2 ih1 ih2 =>
    simp only [compileAST, evalAST]
    rw [List.append_assoc, hexec, ih1, hexec, ih2]
    rfl
  | mul e1 e2 ih1 ih2 =>
    simp only [compileAST, evalAST]
    rw [List.append_assoc, hexec, ih1, hexec, ih2]
    rfl

#print axioms compileAST_correct

end hq_14_arith_vm_compiler

/-! ## 15. Nicomachus's Sum of Cubes Identity 4 * Σ k^3 = (n(n+1))^2 (`nat_number_theory`) -/
namespace hq_15_nicomachus_sum_cubes

def sumCubes : Nat → Nat
  | 0 => 0
  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)

theorem nicomachus_sum_cubes (n : Nat) : 4 * sumCubes n = (n * (n + 1)) * (n * (n + 1)) :=
by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumCubes, Nat.left_distrib, ih]
    have h1 : (k * (k + 1)) * (k * (k + 1)) = (k * k) * ((k + 1) * (k + 1)) := by
      rw [Nat.mul_assoc, ← Nat.mul_assoc (k + 1) k (k + 1), Nat.mul_comm (k + 1) k, Nat.mul_assoc, ← Nat.mul_assoc]
    have h2 : 4 * ((k + 1) * (k + 1) * (k + 1)) = (4 * (k + 1)) * ((k + 1) * (k + 1)) := by
      rw [Nat.mul_comm ((k + 1) * (k + 1)) (k + 1), ← Nat.mul_assoc]
    have h3 : ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) = ((k + 2) * (k + 2)) * ((k + 1) * (k + 1)) := by
      rw [Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, ← Nat.mul_assoc (k + 1) (k + 2) (k + 1)]
      rw [Nat.mul_comm (k + 1) (k + 2), Nat.mul_assoc, ← Nat.mul_assoc]
    have h4 : k * k + 4 * (k + 1) = (k + 2) * (k + 2) := by
      rw [Nat.left_distrib (k + 2) k 2, Nat.right_distrib, Nat.right_distrib]
      omega
    rw [h1, h2, h3, ← Nat.right_distrib, h4]

#print axioms nicomachus_sum_cubes

end hq_15_nicomachus_sum_cubes
