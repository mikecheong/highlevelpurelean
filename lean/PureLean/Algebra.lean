/-!
# PureLean.Algebra

Abstract Algebra: Pure Monoids, Groups, Subgroups, Group Actions, Homomorphisms, and Rings.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.Algebra

namespace Section01

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

theorem ring_mul_neg {R : Type} [PureRing R] (r s : R) : PureRing.mul r (PureRing.neg s) = PureRing.neg (PureRing.mul r s) :=
by
  have hz : PureRing.mul r PureRing.zero = PureRing.zero := by
    have h0 : PureRing.add (PureRing.mul r PureRing.zero) (PureRing.mul r PureRing.zero) = PureRing.add (PureRing.mul r PureRing.zero) PureRing.zero := by
      rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]
    have h0' := congrArg (PureRing.add (PureRing.neg (PureRing.mul r PureRing.zero))) h0
    rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h0'
    exact h0'
  have hsum : PureRing.add (PureRing.mul r s) (PureRing.mul r (PureRing.neg s)) = PureRing.zero := by
    rw [← PureRing.left_distrib, PureRing.add_neg, hz]
  have hfin := congrArg (PureRing.add (PureRing.neg (PureRing.mul r s))) hsum
  rw [← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.add_zero] at hfin
  exact hfin

theorem ring_mul_zero {R : Type} [PureRing R] (a1 : R) : PureRing.mul a1 PureRing.zero = PureRing.zero :=
by
  have h1 : PureRing.add (PureRing.mul a1 PureRing.zero) (PureRing.mul a1 PureRing.zero) = PureRing.add (PureRing.mul a1 PureRing.zero) PureRing.zero := by
    rw [← PureRing.left_distrib, PureRing.add_zero, PureRing.add_zero]
  have h2 := congrArg (PureRing.add (PureRing.neg (PureRing.mul a1 PureRing.zero))) h1
  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h2
  exact h2

theorem ring_add_left_cancel {R : Type} [PureRing R] (a1 a2 a3 : R) (h : PureRing.add a1 a2 = PureRing.add a1 a3) : a2 = a3 :=
by
  have h1 := congrArg (PureRing.add (PureRing.neg a1)) h
  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h1
  exact h1

theorem ring_neg_neg {R : Type} [PureRing R] (x : R) : PureRing.neg (PureRing.neg x) = x :=
by
  calc PureRing.neg (PureRing.neg x)
    _ = PureRing.add (PureRing.neg (PureRing.neg x)) PureRing.zero := by rw [PureRing.add_zero]
    _ = PureRing.add (PureRing.neg (PureRing.neg x)) (PureRing.add (PureRing.neg x) x) := by rw [PureRing.neg_add]
    _ = PureRing.add (PureRing.add (PureRing.neg (PureRing.neg x)) (PureRing.neg x)) x := by rw [← PureRing.add_assoc]
    _ = PureRing.add PureRing.zero x := by rw [PureRing.neg_add]
    _ = x := by rw [PureRing.zero_add]

theorem ring_zero_mul {R : Type} [PureRing R] (x : R) : PureRing.mul PureRing.zero x = PureRing.zero :=
by
  have h1 : PureRing.add (PureRing.mul PureRing.zero x) (PureRing.mul PureRing.zero x) = PureRing.add (PureRing.mul PureRing.zero x) PureRing.zero := by
    rw [← PureRing.right_distrib, PureRing.zero_add, PureRing.add_zero]
  have h2 := congrArg (PureRing.add (PureRing.neg (PureRing.mul PureRing.zero x))) h1
  rw [← PureRing.add_assoc, ← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.zero_add] at h2
  exact h2

theorem ring_distrib_four {R : Type} [PureRing R] (u v w d : R) : PureRing.mul (PureRing.add u v) (PureRing.add w d) = PureRing.add (PureRing.add (PureRing.mul u w) (PureRing.mul u d)) (PureRing.add (PureRing.mul v w) (PureRing.mul v d)) :=
by
  rw [PureRing.right_distrib, PureRing.left_distrib, PureRing.left_distrib]

theorem ring_neg_eq_of_add_zero {R : Type} [PureRing R] (e1 e2 : R) (h : PureRing.add e1 e2 = PureRing.zero) : e2 = PureRing.neg e1 :=
by
  have h1 := congrArg (PureRing.add (PureRing.neg e1)) h
  rw [← PureRing.add_assoc, PureRing.neg_add, PureRing.zero_add, PureRing.add_zero] at h1
  exact h1

end Section01

namespace Section02

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
  PureGroup.mul (PureGroup.mul g x) (PureGroup.inv g)

theorem group_eq_inv_mul_of_mul_eq {G : Type} [PureGroup G] (x y z : G) (h : PureGroup.mul x y = z) : y = PureGroup.mul (PureGroup.inv x) z :=
by
  rw [← h, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul]

theorem conj_mul {G : Type} [PureGroup G] (s t d : G) : conj s (PureGroup.mul t d) = PureGroup.mul (conj s t) (conj s d) :=
by
  unfold conj
  rw [PureGroup.mul_assoc (PureGroup.mul s t) (PureGroup.inv s) (PureGroup.mul (PureGroup.mul s d) (PureGroup.inv s))]
  rw [← PureGroup.mul_assoc (PureGroup.inv s) (PureGroup.mul s d) (PureGroup.inv s)]
  rw [← PureGroup.mul_assoc (PureGroup.inv s) s d]
  rw [PureGroup.inv_mul, PureGroup.one_mul]
  rw [← PureGroup.mul_assoc (PureGroup.mul s t) d (PureGroup.inv s)]
  rw [PureGroup.mul_assoc s t d]

theorem group_eq_mul_inv_of_mul_eq {G : Type} [PureGroup G] (x y z : G) (h : PureGroup.mul x y = z) : x = PureGroup.mul z (PureGroup.inv y) :=
by
  rw [← h, PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one]

theorem group_inv_cancel_right {G : Type} [PureGroup G] (a b : G) : PureGroup.mul (PureGroup.mul a (PureGroup.inv b)) b = a :=
by
  rw [PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.mul_one]

theorem conj_one {G : Type} [PureGroup G] (s : G) : conj s PureGroup.one = PureGroup.one :=
by
  unfold conj
  rw [PureGroup.mul_one, PureGroup.mul_inv]

theorem group_mul_inv_cancel_left {G : Type} [PureGroup G] (a b : G) : PureGroup.mul a (PureGroup.mul (PureGroup.inv a) b) = b :=
by
  rw [← PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.one_mul]

theorem group_mul_inv_cancel_right {G : Type} [PureGroup G] (p q : G) : PureGroup.mul (PureGroup.mul p q) (PureGroup.inv q) = p :=
by
  rw [PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one]

theorem group_left_cancel {G : Type} [PureGroup G] (x y z : G) (h : PureGroup.mul x y = PureGroup.mul x z) : y = z :=
by
  have h1 : PureGroup.mul (PureGroup.inv x) (PureGroup.mul x y) = PureGroup.mul (PureGroup.inv x) (PureGroup.mul x z) := congrArg (PureGroup.mul (PureGroup.inv x)) h
  rw [← PureGroup.mul_assoc, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.one_mul] at h1
  exact h1

theorem group_inv_inv {G : Type} [PureGroup G] (x : G) : PureGroup.inv (PureGroup.inv x) = x :=
by
  calc PureGroup.inv (PureGroup.inv x)
    _ = PureGroup.mul (PureGroup.inv (PureGroup.inv x)) PureGroup.one := by rw [PureGroup.mul_one]
    _ = PureGroup.mul (PureGroup.inv (PureGroup.inv x)) (PureGroup.mul (PureGroup.inv x) x) := by rw [PureGroup.inv_mul]
    _ = PureGroup.mul (PureGroup.mul (PureGroup.inv (PureGroup.inv x)) (PureGroup.inv x)) x := by rw [← PureGroup.mul_assoc]
    _ = PureGroup.mul PureGroup.one x := by rw [PureGroup.inv_mul]
    _ = x := by rw [PureGroup.one_mul]

theorem group_right_cancel {G : Type} [PureGroup G] (p q r : G) (h : PureGroup.mul q p = PureGroup.mul r p) : q = r :=
by
  have h1 : PureGroup.mul (PureGroup.mul q p) (PureGroup.inv p) = PureGroup.mul (PureGroup.mul r p) (PureGroup.inv p) := congrArg (fun t => PureGroup.mul t (PureGroup.inv p)) h
  rw [PureGroup.mul_assoc, PureGroup.mul_assoc, PureGroup.mul_inv, PureGroup.mul_one, PureGroup.mul_one] at h1
  exact h1

theorem group_inv_mul_cancel_left {G : Type} [PureGroup G] (p q : G) : PureGroup.mul (PureGroup.inv p) (PureGroup.mul p q) = q :=
by
  rw [← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul]

end Section02

namespace Section03

def Involutive {α : Type} (f : α → α) : Prop := ∀ x, f (f x) = x
def IdempotentFn {α : Type} (f : α → α) : Prop := ∀ x, f (f x) = f x
def Commutes {α : Type} (f g : α → α) : Prop := ∀ x, f (g x) = g (f x)

theorem commutes_symm {α : Type} (u v : α → α) (hc : Commutes u v) : Commutes v u :=
by
  intro x
  exact (hc x).symm

theorem commutes_self_iter2 {α : Type} (f g : α → α) (hc : Commutes f g) : Commutes f (fun x => g (g x)) :=
by
  intro x
  dsimp
  rw [hc (g x), hc x]

theorem invol_injective {α : Type} (f : α → α) (hf : Involutive f) (x y : α) (h : f x = f y) : x = y :=
by
  have h1 := congrArg f h
  rw [hf x, hf y] at h1
  exact h1

theorem invol_triple {α : Type} (p : α → α) (hf : Involutive p) (x : α) : p (p (p x)) = p x :=
by
  rw [hf x]

theorem invol_quad {α : Type} (φ : α → α) (hf : Involutive φ) (x : α) : φ (φ (φ (φ x))) = x :=
by
  rw [hf x, hf x]

theorem invol_surjective {α : Type} (r1 : α → α) (hf : Involutive r1) (y : α) : ∃ x, r1 x = y :=
by
  exact ⟨r1 y, hf y⟩

end Section03

namespace Section04

class PureMonoid (M : Type) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

def mpow {M : Type} [PureMonoid M] (a : M) : Nat → M
  | 0 => PureMonoid.one
  | n + 1 => PureMonoid.mul (mpow a n) a

class PureCommMonoid (M : Type) extends PureMonoid M where
  mul_comm : ∀ a b : M, mul a b = mul b a

theorem comm_monoid_outer_flip {M : Type} [PureCommMonoid M] (a b c d : M) : PureMonoid.mul (PureMonoid.mul a b) (PureMonoid.mul c d) = PureMonoid.mul (PureMonoid.mul d c) (PureMonoid.mul b a) :=
by
  rw [PureCommMonoid.mul_comm a b, PureCommMonoid.mul_comm c d]
  rw [PureCommMonoid.mul_comm (PureMonoid.mul b a) (PureMonoid.mul d c)]

theorem comm_monoid_swap_inner {M : Type} [PureCommMonoid M] (p q r s : M) : PureMonoid.mul (PureMonoid.mul p q) (PureMonoid.mul r s) = PureMonoid.mul (PureMonoid.mul p r) (PureMonoid.mul q s) :=
by
  rw [PureMonoid.mul_assoc p q (PureMonoid.mul r s)]
  rw [← PureMonoid.mul_assoc q r s]
  rw [PureCommMonoid.mul_comm q r]
  rw [PureMonoid.mul_assoc r q s]
  rw [← PureMonoid.mul_assoc p r (PureMonoid.mul q s)]

theorem comm_monoid_perm3 {M : Type} [PureCommMonoid M] (a b c : M) : PureMonoid.mul (PureMonoid.mul a b) c = PureMonoid.mul (PureMonoid.mul c b) a :=
by
  rw [PureCommMonoid.mul_comm a b, PureCommMonoid.mul_comm (PureMonoid.mul b a) c, PureMonoid.mul_assoc]

end Section04

namespace Section05

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
  PureGroup.mul (PureGroup.mul g x) (PureGroup.inv g)

class GroupAction (G X : Type) [PureGroup G] where
  act : G → X → X
  one_act : ∀ x : X, act PureGroup.one x = x
  mul_act : ∀ g h : G, ∀ x : X, act (PureGroup.mul g h) x = act g (act h x)

theorem action_injective {G X : Type} [PureGroup G] [GroupAction G X] (g : G) (x y : X) (h : GroupAction.act g x = GroupAction.act g y) : x = y :=
by
  have h1 := congrArg (GroupAction.act (PureGroup.inv g)) h
  rw [← GroupAction.mul_act, ← GroupAction.mul_act, PureGroup.inv_mul, GroupAction.one_act, GroupAction.one_act] at h1
  exact h1

theorem action_mul_inv_cancel {G X : Type} [PureGroup G] [GroupAction G X] (g : G) (x : X) : GroupAction.act g (GroupAction.act (PureGroup.inv g) x) = x :=
by
  rw [← GroupAction.mul_act, PureGroup.mul_inv, GroupAction.one_act]

theorem action_inv_cancel {G X : Type} [PureGroup G] [GroupAction G X] (g : G) (x : X) : GroupAction.act (PureGroup.inv g) (GroupAction.act g x) = x :=
by
  rw [← GroupAction.mul_act, PureGroup.inv_mul, GroupAction.one_act]

end Section05

namespace Section06

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
  inv_mem : ∀ {a}, S a → S (PureGrp.inv a)

theorem subgroup_mul_inv_mem {G : Type} [PureGrp G] (H : G → Prop) (hH : IsSubgroup H) {x y : G} (hx : H x) (hy : H y) : H (PureGrp.mul x (PureGrp.inv y)) :=
by
  exact hH.mul_mem hx (hH.inv_mem hy)

theorem subgroup_of_one_and_div {G : Type} [PureGrp G] (S : G → Prop) (hone : S PureGrp.one) (hdiv : ∀ {x y}, S x → S y → S (PureGrp.mul x (PureGrp.inv y))) : IsSubgroup S :=
by
  have hinv : ∀ {a : G}, S a → S (PureGrp.inv a) := by
    intro a ha
    have h1 := hdiv hone ha
    rw [PureGrp.one_mul] at h1
    exact h1
  have hinv2 : ∀ b : G, PureGrp.inv (PureGrp.inv b) = b := by
    intro b
    calc PureGrp.inv (PureGrp.inv b)
      _ = PureGrp.mul (PureGrp.inv (PureGrp.inv b)) PureGrp.one := by rw [PureGrp.mul_one]
      _ = PureGrp.mul (PureGrp.inv (PureGrp.inv b)) (PureGrp.mul (PureGrp.inv b) b) := by rw [PureGrp.inv_mul]
      _ = PureGrp.mul (PureGrp.mul (PureGrp.inv (PureGrp.inv b)) (PureGrp.inv b)) b := by rw [← PureGrp.mul_assoc]
      _ = b := by rw [PureGrp.inv_mul, PureGrp.one_mul]
  refine ⟨hone, ?_, hinv⟩
  intro a b ha hb
  have h2 := hdiv ha (hinv hb)
  rw [hinv2 b] at h2
  exact h2

theorem subgroup_inter {G : Type} [PureGrp G] (H K : G → Prop) (hH : IsSubgroup H) (hK : IsSubgroup K) : IsSubgroup (fun x => H x ∧ K x) :=
by
  refine ⟨⟨hH.one_mem, hK.one_mem⟩, ?_, ?_⟩
  · rintro a b ⟨haH, haK⟩ ⟨hbH, hbK⟩
    exact ⟨hH.mul_mem haH hbH, hK.mul_mem haK hbK⟩
  · rintro a ⟨haH, haK⟩
    exact ⟨hH.inv_mem haH, hK.inv_mem haK⟩

end Section06

namespace Section07

class PureMonoid (M : Type) where
  mul : M → M → M
  one : M
  mul_assoc : ∀ a b c : M, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : M, mul one a = a
  mul_one : ∀ a : M, mul a one = a

def mpow {M : Type} [PureMonoid M] (a : M) : Nat → M
  | 0 => PureMonoid.one
  | n + 1 => PureMonoid.mul (mpow a n) a

theorem mpow_one_const {M : Type} [PureMonoid M] : mpow (PureMonoid.one : M) 6 = PureMonoid.one :=
by
  simp [mpow, PureMonoid.one_mul]

theorem monoid_assoc4_ll_to_rr {M : Type} [PureMonoid M] (p q r s : M) : PureMonoid.mul (PureMonoid.mul (PureMonoid.mul p q) r) s = PureMonoid.mul p (PureMonoid.mul q (PureMonoid.mul r s)) :=
by
  rw [PureMonoid.mul_assoc, PureMonoid.mul_assoc]

theorem idempotent_mpow_succ {M : Type} [PureMonoid M] (a : M) (hidem : PureMonoid.mul a a = a) (n : Nat) : mpow a (n + 1) = a :=
by
  induction n with
  | zero => simp [mpow, PureMonoid.one_mul]
  | succ k ih =>
    change PureMonoid.mul (mpow a (k + 1)) a = a
    rw [ih, hidem]

theorem monoid_assoc4_mid_to_lr {M : Type} [PureMonoid M] (g1 g2 g3 g4 : M) : PureMonoid.mul (PureMonoid.mul g1 (PureMonoid.mul g2 g3)) g4 = PureMonoid.mul (PureMonoid.mul g1 g2) (PureMonoid.mul g3 g4) :=
by
  rw [← PureMonoid.mul_assoc g1 g2 g3, PureMonoid.mul_assoc]

theorem mpow_add {M : Type} [PureMonoid M] (x : M) (m n : Nat) : mpow x (m + n) = PureMonoid.mul (mpow x m) (mpow x n) :=
by
  induction n with
  | zero =>
    simp [mpow, PureMonoid.mul_one]
  | succ k ih =>
    rw [Nat.add_succ, mpow, mpow, ih, PureMonoid.mul_assoc]

theorem mpow_succ_left {M : Type} [PureMonoid M] (u : M) (n : Nat) : PureMonoid.mul u (mpow u n) = PureMonoid.mul (mpow u n) u :=
by
  induction n with
  | zero => simp [mpow, PureMonoid.mul_one, PureMonoid.one_mul]
  | succ k ih =>
    calc PureMonoid.mul u (PureMonoid.mul (mpow u k) u)
      _ = PureMonoid.mul (PureMonoid.mul u (mpow u k)) u := by rw [← PureMonoid.mul_assoc]
      _ = PureMonoid.mul (PureMonoid.mul (mpow u k) u) u := by rw [ih]

theorem mpow_one_all {M : Type} [PureMonoid M] (n : Nat) : mpow (PureMonoid.one : M) n = PureMonoid.one :=
by
  induction n with
  | zero => rfl
  | succ k ih => simp [mpow, ih, PureMonoid.one_mul]

theorem monoid_one_absorb_mid {M : Type} [PureMonoid M] (u v w : M) : PureMonoid.mul u (PureMonoid.mul PureMonoid.one (PureMonoid.mul v w)) = PureMonoid.mul (PureMonoid.mul u v) w :=
by
  rw [PureMonoid.one_mul, PureMonoid.mul_assoc]

theorem monoid_reassoc_one {M : Type} [PureMonoid M] (x y z : M) : PureMonoid.mul (PureMonoid.mul x PureMonoid.one) (PureMonoid.mul y z) = PureMonoid.mul (PureMonoid.mul x y) z :=
by
  rw [PureMonoid.mul_one, PureMonoid.mul_assoc]

end Section07

namespace Section08

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
  PureGroup.mul (PureGroup.mul g x) (PureGroup.inv g)

structure GroupHom (G H : Type) [PureGroup G] [PureGroup H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (PureGroup.mul a b) = PureGroup.mul (toFun a) (toFun b)

theorem hom_map_one {G H : Type} [PureGroup G] [PureGroup H] (p : GroupHom G H) : p.toFun PureGroup.one = PureGroup.one :=
by
  have h1 : PureGroup.mul (p.toFun PureGroup.one) (p.toFun PureGroup.one) = PureGroup.mul (p.toFun PureGroup.one) PureGroup.one := by
    rw [← p.map_mul, PureGroup.one_mul, PureGroup.mul_one]
  have h2 := congrArg (PureGroup.mul (PureGroup.inv (p.toFun PureGroup.one))) h1
  rw [← PureGroup.mul_assoc, ← PureGroup.mul_assoc, PureGroup.inv_mul, PureGroup.one_mul, PureGroup.one_mul] at h2
  exact h2

theorem hom_map_mul3 {G H : Type} [PureGroup G] [PureGroup H] (f : GroupHom G H) (x y z : G) : f.toFun (PureGroup.mul (PureGroup.mul x y) z) = PureGroup.mul (f.toFun x) (PureGroup.mul (f.toFun y) (f.toFun z)) :=
by
  rw [f.map_mul, f.map_mul, PureGroup.mul_assoc]

theorem hom_comp_mul {G H K : Type} [PureGroup G] [PureGroup H] [PureGroup K] (f : GroupHom G H) (g : GroupHom H K) (x y : G) : g.toFun (f.toFun (PureGroup.mul x y)) = PureGroup.mul (g.toFun (f.toFun x)) (g.toFun (f.toFun y)) :=
by
  rw [f.map_mul, g.map_mul]

end Section08

end PureLean.Algebra
