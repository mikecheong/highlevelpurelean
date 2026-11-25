/-!
# PureLean.OrderGalois

Order Theory: Posets, Lattices, Galois Connections, Closure Operators, and Heyting Algebras.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.OrderGalois

namespace Section01

class PurePoset (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

def MonoMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f x) (f y)

def AntiMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f y) (f x)

class PureLattice (L : Type) extends PurePoset L where
  sup : L → L → L
  inf : L → L → L
  le_sup_left : ∀ a b : L, le a (sup a b)
  le_sup_right : ∀ a b : L, le b (sup a b)
  sup_le : ∀ {a b c : L}, le a c → le b c → le (sup a b) c
  inf_le_left : ∀ a b : L, le (inf a b) a
  inf_le_right : ∀ a b : L, le (inf a b) b
  le_inf : ∀ {a b c : L}, le a b → le a c → le a (inf b c)

theorem lattice_sup_comm {L : Type} [PureLattice L] (t1 t2 : L) : PureLattice.sup t1 t2 = PureLattice.sup t2 t1 :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.sup_le (PureLattice.le_sup_right t2 t1) (PureLattice.le_sup_left t2 t1)
  · exact PureLattice.sup_le (PureLattice.le_sup_right t1 t2) (PureLattice.le_sup_left t1 t2)

theorem lattice_le_iff_inf_eq {L : Type} [PureLattice L] (a b : L) : PurePoset.le a b ↔ PureLattice.inf a b = a :=
by
  constructor
  · intro h
    apply PurePoset.le_antisymm
    · exact PureLattice.inf_le_left a b
    · exact PureLattice.le_inf (PurePoset.le_refl a) h
  · intro h
    rw [← h]
    exact PureLattice.inf_le_right a b

theorem lattice_absorb_inf_sup {L : Type} [PureLattice L] (u v : L) : PureLattice.inf u (PureLattice.sup u v) = u :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.inf_le_left u (PureLattice.sup u v)
  · exact PureLattice.le_inf (PurePoset.le_refl u) (PureLattice.le_sup_left u v)

theorem lattice_le_iff_sup_eq {L : Type} [PureLattice L] (x y : L) : PurePoset.le x y ↔ PureLattice.sup x y = y :=
by
  constructor
  · intro h
    apply PurePoset.le_antisymm
    · exact PureLattice.sup_le h (PurePoset.le_refl y)
    · exact PureLattice.le_sup_right x y
  · intro h
    rw [← h]
    exact PureLattice.le_sup_left x y

theorem lattice_inf_mono {L : Type} [PureLattice L] (l1 l2 l3 l4 : L) (h1 : PurePoset.le l1 l3) (h2 : PurePoset.le l2 l4) : PurePoset.le (PureLattice.inf l1 l2) (PureLattice.inf l3 l4) :=
by
  apply PureLattice.le_inf
  · exact PurePoset.le_trans (PureLattice.inf_le_left l1 l2) h1
  · exact PurePoset.le_trans (PureLattice.inf_le_right l1 l2) h2

theorem lattice_inf_comm {L : Type} [PureLattice L] (p q : L) : PureLattice.inf p q = PureLattice.inf q p :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.le_inf (PureLattice.inf_le_right p q) (PureLattice.inf_le_left p q)
  · exact PureLattice.le_inf (PureLattice.inf_le_right q p) (PureLattice.inf_le_left q p)

theorem lattice_sup_mono {L : Type} [PureLattice L] (x y z w : L) (h1 : PurePoset.le x z) (h2 : PurePoset.le y w) : PurePoset.le (PureLattice.sup x y) (PureLattice.sup z w) :=
by
  apply PureLattice.sup_le
  · exact PurePoset.le_trans h1 (PureLattice.le_sup_left z w)
  · exact PurePoset.le_trans h2 (PureLattice.le_sup_right z w)

theorem lattice_absorb_sup_inf {L : Type} [PureLattice L] (t1 t2 : L) : PureLattice.sup t1 (PureLattice.inf t1 t2) = t1 :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.sup_le (PurePoset.le_refl t1) (PureLattice.inf_le_left t1 t2)
  · exact PureLattice.le_sup_left t1 (PureLattice.inf t1 t2)

theorem lattice_distrib_le {L : Type} [PureLattice L] (u v k : L) : PurePoset.le (PureLattice.sup (PureLattice.inf u v) (PureLattice.inf u k)) (PureLattice.inf u (PureLattice.sup v k)) :=
by
  apply PureLattice.le_inf
  · exact PureLattice.sup_le (PureLattice.inf_le_left u v) (PureLattice.inf_le_left u k)
  · apply PureLattice.sup_le
    · exact PurePoset.le_trans (PureLattice.inf_le_right u v) (PureLattice.le_sup_left v k)
    · exact PurePoset.le_trans (PureLattice.inf_le_right u k) (PureLattice.le_sup_right v k)

theorem lattice_sup_idem {L : Type} [PureLattice L] (p : L) : PureLattice.sup p p = p :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.sup_le (PurePoset.le_refl p) (PurePoset.le_refl p)
  · exact PureLattice.le_sup_left p p

theorem lattice_sup_inf_le {L : Type} [PureLattice L] (p q r : L) : PurePoset.le (PureLattice.sup p (PureLattice.inf q r)) (PureLattice.inf (PureLattice.sup p q) (PureLattice.sup p r)) :=
by
  apply PureLattice.le_inf
  · apply PureLattice.sup_le (PureLattice.le_sup_left p q)
    exact PurePoset.le_trans (PureLattice.inf_le_left q r) (PureLattice.le_sup_right p q)
  · apply PureLattice.sup_le (PureLattice.le_sup_left p r)
    exact PurePoset.le_trans (PureLattice.inf_le_right q r) (PureLattice.le_sup_right p r)

theorem lattice_inf_idem {L : Type} [PureLattice L] (s1 : L) : PureLattice.inf s1 s1 = s1 :=
by
  apply PurePoset.le_antisymm
  · exact PureLattice.inf_le_left s1 s1
  · exact PureLattice.le_inf (PurePoset.le_refl s1) (PurePoset.le_refl s1)

end Section01

namespace Section02

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

theorem heyting_himp_inf_right {H : Type} [HeytingAlg H] (p q r : H) : HeytingAlg.himp p (BoundedLattice.inf q r) = BoundedLattice.inf (HeytingAlg.himp p q) (HeytingAlg.himp p r) :=
by
  have hmp_bc : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp p (BoundedLattice.inf q r)) p) (BoundedLattice.inf q r) := (HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _)
  apply BoundedLattice.le_antisymm
  · apply BoundedLattice.le_inf
    · exact (HeytingAlg.le_himp_iff _ _ _).mpr (BoundedLattice.le_trans hmp_bc (BoundedLattice.inf_le_left _ _))
    · exact (HeytingAlg.le_himp_iff _ _ _).mpr (BoundedLattice.le_trans hmp_bc (BoundedLattice.inf_le_right _ _))
  · apply (HeytingAlg.le_himp_iff _ _ _).mpr
    apply BoundedLattice.le_inf
    · have hl : BoundedLattice.le (BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp p q) (HeytingAlg.himp p r)) p) (BoundedLattice.inf (HeytingAlg.himp p q) p) := by
        apply BoundedLattice.le_inf
        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_left _ _)
        · exact BoundedLattice.inf_le_right _ _
      exact BoundedLattice.le_trans hl ((HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _))
    · have hr : BoundedLattice.le (BoundedLattice.inf (BoundedLattice.inf (HeytingAlg.himp p q) (HeytingAlg.himp p r)) p) (BoundedLattice.inf (HeytingAlg.himp p r) p) := by
        apply BoundedLattice.le_inf
        · exact BoundedLattice.le_trans (BoundedLattice.inf_le_left _ _) (BoundedLattice.inf_le_right _ _)
        · exact BoundedLattice.inf_le_right _ _
      exact BoundedLattice.le_trans hr ((HeytingAlg.le_himp_iff _ _ _).mp (BoundedLattice.le_refl _))

theorem bdd_inf_bot {L : Type} [BoundedLattice L] (a : L) : BoundedLattice.inf a BoundedLattice.bot = BoundedLattice.bot :=
by
  apply BoundedLattice.le_antisymm
  · exact BoundedLattice.inf_le_right a BoundedLattice.bot
  · exact BoundedLattice.bot_le _

theorem heyting_self_top {H : Type} [HeytingAlg H] (g1 : H) : HeytingAlg.himp g1 g1 = BoundedLattice.top :=
by
  apply BoundedLattice.le_antisymm
  · exact BoundedLattice.le_top _
  · exact (HeytingAlg.le_himp_iff BoundedLattice.top g1 g1).mpr (BoundedLattice.inf_le_right _ _)

theorem bdd_sup_top {L : Type} [BoundedLattice L] (a : L) : BoundedLattice.sup a BoundedLattice.top = BoundedLattice.top :=
by
  apply BoundedLattice.le_antisymm
  · exact BoundedLattice.le_top _
  · exact BoundedLattice.le_sup_right a BoundedLattice.top

theorem bdd_sup_bot {L : Type} [BoundedLattice L] (k1 : L) : BoundedLattice.sup k1 BoundedLattice.bot = k1 :=
by
  apply BoundedLattice.le_antisymm
  · exact BoundedLattice.sup_le (BoundedLattice.le_refl k1) (BoundedLattice.bot_le k1)
  · exact BoundedLattice.le_sup_left k1 BoundedLattice.bot

theorem heyting_mono_right {H : Type} [HeytingAlg H] (t1 t2 t3 : H) (hbc : BoundedLattice.le t2 t3) : BoundedLattice.le (HeytingAlg.himp t1 t2) (HeytingAlg.himp t1 t3) :=
by
  apply (HeytingAlg.le_himp_iff _ t1 t3).mpr
  have hmp : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp t1 t2) t1) t2 := (HeytingAlg.le_himp_iff _ t1 t2).mp (BoundedLattice.le_refl _)
  exact BoundedLattice.le_trans hmp hbc

theorem heyting_modus_ponens {H : Type} [HeytingAlg H] (e1 e2 : H) : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp e1 e2) e1) e2 :=
by
  exact (HeytingAlg.le_himp_iff (HeytingAlg.himp e1 e2) e1 e2).mp (BoundedLattice.le_refl _)

theorem bdd_inf_top {L : Type} [BoundedLattice L] (n1 : L) : BoundedLattice.inf n1 BoundedLattice.top = n1 :=
by
  apply BoundedLattice.le_antisymm
  · exact BoundedLattice.inf_le_left n1 BoundedLattice.top
  · exact BoundedLattice.le_inf (BoundedLattice.le_refl n1) (BoundedLattice.le_top n1)

theorem heyting_anti_left {H : Type} [HeytingAlg H] (u v w : H) (hab : BoundedLattice.le u v) : BoundedLattice.le (HeytingAlg.himp v w) (HeytingAlg.himp u w) :=
by
  apply (HeytingAlg.le_himp_iff _ u w).mpr
  have h1 : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp v w) u) (BoundedLattice.inf (HeytingAlg.himp v w) v) := by
    apply BoundedLattice.le_inf (BoundedLattice.inf_le_left _ _)
    exact BoundedLattice.le_trans (BoundedLattice.inf_le_right _ _) hab
  have hmp : BoundedLattice.le (BoundedLattice.inf (HeytingAlg.himp v w) v) w := (HeytingAlg.le_himp_iff _ v w).mp (BoundedLattice.le_refl _)
  exact BoundedLattice.le_trans h1 hmp

end Section02

namespace Section03

class PurePoset (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

def MonoMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f x) (f y)

def AntiMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f y) (f x)

structure GaloisConn (A B : Type) [PurePoset A] [PurePoset B] (l : A → B) (u : B → A) : Prop where
  adj : ∀ a b, PurePoset.le (l a) b ↔ PurePoset.le a (u b)

structure ClosureOp (P : Type) [PurePoset P] (cl : P → P) : Prop where
  extensive : ∀ x, PurePoset.le x (cl x)
  monotone : ∀ {x y}, PurePoset.le x y → PurePoset.le (cl x) (cl y)
  idempotent : ∀ x, cl (cl x) = cl x

theorem galois_lower_mono {A B : Type} [PurePoset A] [PurePoset B] (low : A → B) (upp : B → A) (hgc : GaloisConn A B low upp) : MonoMap low :=
by
  intro x y hxy
  have hy : PurePoset.le y (upp (low y)) := (hgc.adj y (low y)).mp (PurePoset.le_refl (low y))
  exact (hgc.adj x (low y)).mpr (PurePoset.le_trans hxy hy)

theorem galois_l_u_l {A B : Type} [PurePoset A] [PurePoset B] (sh : A → B) (fl : B → A) (hgc : GaloisConn A B sh fl) (a : A) : sh (fl (sh a)) = sh a :=
by
  apply PurePoset.le_antisymm
  · exact (hgc.adj (fl (sh a)) (sh a)).mpr (PurePoset.le_refl (fl (sh a)))
  · have ha : PurePoset.le a (fl (sh a)) := (hgc.adj a (sh a)).mp (PurePoset.le_refl (sh a))
    have hu : PurePoset.le (fl (sh a)) (fl (sh (fl (sh a)))) := (hgc.adj (fl (sh a)) (sh (fl (sh a)))).mp (PurePoset.le_refl _)
    exact (hgc.adj a (sh (fl (sh a)))).mpr (PurePoset.le_trans ha hu)

theorem galois_closure_op {A B : Type} [PurePoset A] [PurePoset B] (c_ : A → B) (k_ : B → A) (hgc : GaloisConn A B c_ k_) : ClosureOp A (fun a => k_ (c_ a)) :=
by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact (hgc.adj a (c_ a)).mp (PurePoset.le_refl (c_ a))
  · intro x y hxy
    have hy : PurePoset.le y (k_ (c_ y)) := (hgc.adj y (c_ y)).mp (PurePoset.le_refl (c_ y))
    have hl : PurePoset.le (c_ x) (c_ y) := (hgc.adj x (c_ y)).mpr (PurePoset.le_trans hxy hy)
    have hc : PurePoset.le (c_ (k_ (c_ x))) (c_ x) := (hgc.adj (k_ (c_ x)) (c_ x)).mpr (PurePoset.le_refl _)
    exact (hgc.adj (k_ (c_ x)) (c_ y)).mp (PurePoset.le_trans hc hl)
  · intro a
    apply PurePoset.le_antisymm
    · have hc1 : PurePoset.le (c_ (k_ (c_ a))) (c_ a) := (hgc.adj (k_ (c_ a)) (c_ a)).mpr (PurePoset.le_refl _)
      have hc2 : PurePoset.le (c_ (k_ (c_ (k_ (c_ a))))) (c_ (k_ (c_ a))) := (hgc.adj _ _).mpr (PurePoset.le_refl _)
      exact (hgc.adj _ (c_ a)).mp (PurePoset.le_trans hc2 hc1)
    · exact (hgc.adj (k_ (c_ a)) (c_ (k_ (c_ a)))).mp (PurePoset.le_refl _)

theorem galois_unit {A B : Type} [PurePoset A] [PurePoset B] (L1 : A → B) (R1 : B → A) (hgc : GaloisConn A B L1 R1) (a : A) : PurePoset.le a (R1 (L1 a)) :=
by
  exact (hgc.adj a (L1 a)).mp (PurePoset.le_refl (L1 a))

theorem galois_counit {A B : Type} [PurePoset A] [PurePoset B] (f : A → B) (g : B → A) (hgc : GaloisConn A B f g) (b : B) : PurePoset.le (f (g b)) b :=
by
  exact (hgc.adj (g b) b).mpr (PurePoset.le_refl (g b))

theorem closure_fixed_iff {P : Type} [PurePoset P] (α_ : P → P) (hcl : ClosureOp P α_) (x : P) : PurePoset.le (α_ x) x ↔ α_ x = x :=
by
  constructor
  · intro h
    exact PurePoset.le_antisymm h (hcl.extensive x)
  · intro h
    rw [h]
    exact PurePoset.le_refl x

theorem galois_upper_mono {A B : Type} [PurePoset A] [PurePoset B] (L1 : A → B) (R1 : B → A) (hgc : GaloisConn A B L1 R1) : MonoMap R1 :=
by
  intro x y hxy
  have hx : PurePoset.le (L1 (R1 x)) x := (hgc.adj (R1 x) x).mpr (PurePoset.le_refl (R1 x))
  exact (hgc.adj (R1 x) y).mp (PurePoset.le_trans hx hxy)

end Section03

namespace Section04

class PurePoset (P : Type) where
  le : P → P → Prop
  le_refl : ∀ a : P, le a a
  le_trans : ∀ {a b c : P}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : P}, le a b → le b a → a = b

def MonoMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f x) (f y)

def AntiMap {P Q : Type} [PurePoset P] [PurePoset Q] (f : P → Q) : Prop :=
  ∀ {x y : P}, PurePoset.le x y → PurePoset.le (f y) (f x)

theorem anti_comp_mono {P Q R : Type} [PurePoset P] [PurePoset Q] [PurePoset R] (f : P → Q) (g : Q → R) (hf : AntiMap f) (hg : MonoMap g) : AntiMap (fun x => g (f x)) :=
by
  intro x y hxy
  exact hg (hf hxy)

theorem mono_comp_anti {P Q R : Type} [PurePoset P] [PurePoset Q] [PurePoset R] (f : P → Q) (g : Q → R) (hf : MonoMap f) (hg : AntiMap g) : AntiMap (fun x => g (f x)) :=
by
  intro x y hxy
  exact hg (hf hxy)

theorem poset_cycle3_eq {P : Type} [PurePoset P] (x y z : P) (h1 : PurePoset.le x y) (h2 : PurePoset.le y z) (h3 : PurePoset.le z x) : x = y ∧ y = z :=
by
  constructor
  · exact PurePoset.le_antisymm h1 (PurePoset.le_trans h2 h3)
  · exact PurePoset.le_antisymm h2 (PurePoset.le_trans h3 h1)

theorem anti_comp_anti {P Q R : Type} [PurePoset P] [PurePoset Q] [PurePoset R] (f : P → Q) (g : Q → R) (hf : AntiMap f) (hg : AntiMap g) : MonoMap (fun x => g (f x)) :=
by
  intro x y hxy
  exact hg (hf hxy)

theorem mono_comp_mono {P Q R : Type} [PurePoset P] [PurePoset Q] [PurePoset R] (f : P → Q) (g : Q → R) (hf : MonoMap f) (hg : MonoMap g) : MonoMap (fun x => g (f x)) :=
by
  intro x y hxy
  exact hg (hf hxy)

theorem poset_trans4 {P : Type} [PurePoset P] (a b c d : P) (h1 : PurePoset.le a b) (h2 : PurePoset.le b c) (h3 : PurePoset.le c d) : PurePoset.le a d :=
by
  exact PurePoset.le_trans (PurePoset.le_trans h1 h2) h3

end Section04

end PureLean.OrderGalois
