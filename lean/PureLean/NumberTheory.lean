/-!
# PureLean.NumberTheory

Natural Number Recurrences, Closed-Form Series, Divisibility, Parity, and Integer Modular Congruences.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.NumberTheory

namespace Section01

def PureDvd (d n : Nat) : Prop := ∃ k : Nat, n = d * k
def PureEven (n : Nat) : Prop := ∃ k : Nat, n = 2 * k
def PureOdd (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

theorem even_add_even (a b : Nat) (ha : PureEven a) (hb : PureEven b) : PureEven (a + b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  exact ⟨ka + kb, by omega⟩

theorem consec_prod_even (n : Nat) : PureEven (n * (n + 1)) :=
by
  have hpar : PureEven n ∨ PureOdd n := by
    induction n with
    | zero => exact Or.inl ⟨0, rfl⟩
    | succ k ih =>
      rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact Or.inr ⟨m, rfl⟩
      · exact Or.inl ⟨m + 1, by omega⟩
  rcases hpar with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨k * (2 * k + 1), ?_⟩
    rw [Nat.mul_assoc]
  · refine ⟨(2 * k + 1) * (k + 1), ?_⟩
    have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [h1, ← Nat.mul_assoc, Nat.mul_comm (2 * k + 1) 2, Nat.mul_assoc]

theorem nat_dvd_lin_2 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (2 * a + 4 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨2 * ka + 4 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 2 * (d * ka) = d * (2 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 2 d, Nat.mul_assoc]
  have h2 : 4 * (d * kb) = d * (4 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 4 d, Nat.mul_assoc]
  rw [h1, h2]

theorem dvd_refl (a : Nat) : PureDvd a a :=
by
  exact ⟨1, (Nat.mul_one a).symm⟩

theorem nat_dvd_lin_5 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (5 * a + 6 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨5 * ka + 6 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 5 * (d * ka) = d * (5 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 5 d, Nat.mul_assoc]
  have h2 : 6 * (d * kb) = d * (6 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 6 d, Nat.mul_assoc]
  rw [h1, h2]

theorem odd_add_odd (a b : Nat) (ha : PureOdd a) (hb : PureOdd b) : PureEven (a + b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  exact ⟨ka + kb + 1, by omega⟩

theorem nat_dvd_lin_6 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (6 * a + 1 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨6 * ka + 1 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 6 * (d * ka) = d * (6 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 6 d, Nat.mul_assoc]
  have h2 : 1 * (d * kb) = d * (1 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 1 d, Nat.mul_assoc]
  rw [h1, h2]

theorem not_even_and_odd (n : Nat) : ¬ (PureEven n ∧ PureOdd n) :=
by
  rintro ⟨⟨ka, ha⟩, ⟨kb, hb⟩⟩
  omega

theorem even_or_odd (n : Nat) : PureEven n ∨ PureOdd n :=
by
  induction n with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ k ih =>
    rcases ih with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact Or.inr ⟨m, rfl⟩
    · exact Or.inl ⟨m + 1, by omega⟩

theorem nat_dvd_lin_1 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (1 * a + 3 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨1 * ka + 3 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 1 * (d * ka) = d * (1 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 1 d, Nat.mul_assoc]
  have h2 : 3 * (d * kb) = d * (3 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc]
  rw [h1, h2]

theorem nat_dvd_lin_3 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (3 * a + 3 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨3 * ka + 3 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 3 * (d * ka) = d * (3 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc]
  have h2 : 3 * (d * kb) = d * (3 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc]
  rw [h1, h2]

theorem dvd_trans (a b c : Nat) (h1 : PureDvd a b) (h2 : PureDvd b c) : PureDvd a c :=
by
  rcases h1 with ⟨k1, rfl⟩
  rcases h2 with ⟨k2, rfl⟩
  exact ⟨k1 * k2, Nat.mul_assoc a k1 k2⟩

theorem nat_dvd_lin_4 (d a b : Nat) (ha : PureDvd d a) (hb : PureDvd d b) : PureDvd d (4 * a + 3 * b) :=
by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨4 * ka + 3 * kb, ?_⟩
  rw [Nat.left_distrib]
  have h1 : 4 * (d * ka) = d * (4 * ka) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 4 d, Nat.mul_assoc]
  have h2 : 3 * (d * kb) = d * (3 * kb) := by
    rw [← Nat.mul_assoc, Nat.mul_comm 3 d, Nat.mul_assoc]
  rw [h1, h2]

end Section01

namespace Section02

def ModEqInt (m a b : Int) : Prop := ∃ k : Int, a - b = m * k

def powNat (b : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => powNat b n * b

theorem modEq_symm (m a b : Int) (h : ModEqInt m a b) : ModEqInt m b a :=
by
  rcases h with ⟨k, hk⟩
  refine ⟨-k, ?_⟩
  rw [Int.mul_neg]
  omega

theorem modEq_trans (m a b c : Int) (h1 : ModEqInt m a b) (h2 : ModEqInt m b c) : ModEqInt m a c :=
by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  refine ⟨k1 + k2, ?_⟩
  rw [Int.mul_add]
  omega

theorem powNat_mul_base (a b n : Nat) : powNat (a * b) n = powNat a n * powNat b n :=
by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [powNat, ih]
    rw [Nat.mul_assoc (powNat a k) (powNat b k) (a * b)]
    rw [← Nat.mul_assoc (powNat b k) a b]
    rw [Nat.mul_comm (powNat b k) a]
    rw [Nat.mul_assoc a (powNat b k) b]
    rw [← Nat.mul_assoc (powNat a k) a (powNat b k * b)]

theorem modEq_refl (m a : Int) : ModEqInt m a a :=
by
  exact ⟨0, by omega⟩

theorem modEq_sub_compat (m a1 b1 a2 b2 : Int) (h1 : ModEqInt m a1 b1) (h2 : ModEqInt m a2 b2) : ModEqInt m (a1 - a2) (b1 - b2) :=
by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  refine ⟨k1 - k2, ?_⟩
  rw [Int.mul_sub]
  omega

theorem modEq_add_compat (m a1 b1 a2 b2 : Int) (h1 : ModEqInt m a1 b1) (h2 : ModEqInt m a2 b2) : ModEqInt m (a1 + a2) (b1 + b2) :=
by
  rcases h1 with ⟨k1, hk1⟩
  rcases h2 with ⟨k2, hk2⟩
  refine ⟨k1 + k2, ?_⟩
  rw [Int.mul_add]
  omega

theorem powNat_add (b m n : Nat) : powNat b (m + n) = powNat b m * powNat b n :=
by
  induction n with
  | zero => simp [powNat]
  | succ k ih =>
    rw [Nat.add_succ, powNat, powNat, ih, Nat.mul_assoc]

theorem powNat_mul_exp (b m n : Nat) : powNat b (m * n) = powNat (powNat b m) n :=
by
  have hadd : ∀ x y : Nat, powNat b (x + y) = powNat b x * powNat b y := by
    intro x y
    induction y with
    | zero => simp [powNat]
    | succ k ih => rw [Nat.add_succ, powNat, powNat, ih, Nat.mul_assoc]
  induction n with
  | zero => simp [powNat]
  | succ k ih =>
    rw [Nat.mul_succ, hadd, ih, powNat]

end Section02

namespace Section03

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
  | n + 1 => sumFib n + fibN (n + 1)

theorem pow2N_add (m n : Nat) : pow2N (m + n) = pow2N m * pow2N n :=
by
  induction m with
  | zero => simp [pow2N]
  | succ k ih =>
    rw [Nat.succ_add, pow2N, pow2N, ih, Nat.mul_assoc]

theorem sum_odds_sq (n : Nat) : sumOdds n = n * n :=
by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumOdds, ih]
    have h : (k + 1) * (k + 1) = k * k + (2 * k + 1) := by
      rw [Nat.left_distrib, Nat.right_distrib]
      omega
    omega

theorem pow2N_pos (n : Nat) : 1 ≤ pow2N n :=
by
  induction n with
  | zero => decide
  | succ k ih =>
    simp only [pow2N]
    omega

end Section03

namespace Section04

theorem nat_sq_add (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by
  rw [Nat.left_distrib, Nat.right_distrib, Nat.right_distrib]
  rw [Nat.mul_comm b a]
  omega

theorem nat_foil (a b c d : Nat) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
by
  rw [Nat.right_distrib, Nat.left_distrib, Nat.left_distrib]
  omega

theorem nat_lin_comb_6 (x y z : Nat) : 6 * (x + y) + 5 * (y + z) = 6 * x + (11) * y + 5 * z :=
by
  omega

theorem nat_lin_comb_3 (x y z : Nat) : 3 * (x + y) + 5 * (y + z) = 3 * x + (8) * y + 5 * z :=
by
  omega

theorem nat_lin_comb_2 (x y z : Nat) : 2 * (x + y) + 6 * (y + z) = 2 * x + (8) * y + 6 * z :=
by
  omega

theorem nat_lin_comb_4 (x y z : Nat) : 4 * (x + y) + 2 * (y + z) = 4 * x + (6) * y + 2 * z :=
by
  omega

theorem nat_lin_comb_1 (x y z : Nat) : 1 * (x + y) + 1 * (y + z) = 1 * x + (2) * y + 1 * z :=
by
  omega

theorem nat_lin_comb_5 (x y z : Nat) : 5 * (x + y) + 4 * (y + z) = 5 * x + (9) * y + 4 * z :=
by
  omega

end Section04

end PureLean.NumberTheory
