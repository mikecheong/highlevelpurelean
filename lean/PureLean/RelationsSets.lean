/-!
# PureLean.RelationsSets

Set-Predicates, Image/Preimage Adjunctions, Equivalence Relations, Reflexive-Transitive Closures, and Simulations.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.RelationsSets

namespace Section01

def RelP (α : Type) := α → α → Prop
def ReflR {α : Type} (R : RelP α) : Prop := ∀ x, R x x
def SymmR {α : Type} (R : RelP α) : Prop := ∀ {x y}, R x y → R y x
def TransR {α : Type} (R : RelP α) : Prop := ∀ {x y z}, R x y → R y z → R x z
def EquivR {α : Type} (R : RelP α) : Prop := ReflR R ∧ SymmR R ∧ TransR R

inductive StarR {α : Type} (R : RelP α) : α → α → Prop where
  | refl (x : α) : StarR R x x
  | step {x y z : α} : R x y → StarR R y z → StarR R x z

theorem star_snoc {α : Type} (P : RelP α) {x y z : α} (h1 : StarR P x y) (h2 : P y z) : StarR P x z :=
by
  induction h1 with
  | refl _ => exact StarR.step h2 (StarR.refl z)
  | step hr _ ih => exact StarR.step hr (ih h2)

theorem star_idem {α : Type} (U : RelP α) {x y : α} (h : StarR (StarR U) x y) : StarR U x y :=
by
  have htrans : ∀ {a b c : α}, StarR U a b → StarR U b c → StarR U a c := by
    intro a b c hab hbc
    induction hab with
    | refl _ => exact hbc
    | step hr _ ih => exact StarR.step hr (ih hbc)
  induction h with
  | refl a => exact StarR.refl a
  | step hstar _ ih => exact htrans hstar ih

theorem star_hom_lift {α β : Type} (M1 : RelP α) (T : RelP β) (f : α → β) (hf : ∀ x y, M1 x y → T (f x) (f y)) {x y : α} (h : StarR M1 x y) : StarR T (f x) (f y) :=
by
  induction h with
  | refl a => exact StarR.refl (f a)
  | step hr _ ih => exact StarR.step (hf _ _ hr) ih

theorem star_sub_of_refl_trans {α : Type} (T1 T2 : RelP α) (hrefl : ReflR T2) (htrans : TransR T2) (hsub : ∀ x y, T1 x y → T2 x y) {x y : α} (h : StarR T1 x y) : T2 x y :=
by
  induction h with
  | refl a => exact hrefl a
  | step hr _ ih => exact htrans (hsub _ _ hr) ih

theorem star_mono {α : Type} (T1 T2 : RelP α) (hsub : ∀ x y, T1 x y → T2 x y) {x y : α} (h : StarR T1 x y) : StarR T2 x y :=
by
  induction h with
  | refl a => exact StarR.refl a
  | step hr _ ih => exact StarR.step (hsub _ _ hr) ih

theorem star_symm_of_symm {α : Type} (U : RelP α) (hsym : SymmR U) {x y : α} (h : StarR U x y) : StarR U y x :=
by
  have hsnoc : ∀ {a b c : α}, StarR U a b → U b c → StarR U a c := by
    intro a b c hab hbc
    induction hab with
    | refl _ => exact StarR.step hbc (StarR.refl c)
    | step hr _ ih => exact StarR.step hr (ih hbc)
  induction h with
  | refl a => exact StarR.refl a
  | step hr _ ih => exact hsnoc ih (hsym hr)

theorem star_trans {α : Type} (U : RelP α) {x y z : α} (h1 : StarR U x y) (h2 : StarR U y z) : StarR U x z :=
by
  induction h1 with
  | refl _ => exact h2
  | step hr _ ih => exact StarR.step hr (ih h2)

theorem kernel_equiv {α β : Type} (f : α → β) : EquivR (fun x y => f x = f y) :=
by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro _ _ h; exact h.symm
  · intro _ _ _ h1 h2; exact h1.trans h2

theorem equiv_inter {α : Type} (P Q : RelP α) (hr : EquivR P) (hs : EquivR Q) : EquivR (fun x y => P x y ∧ Q x y) :=
by
  rcases hr with ⟨r_refl, r_symm, r_trans⟩
  rcases hs with ⟨s_refl, s_symm, s_trans⟩
  refine ⟨fun x => ⟨r_refl x, s_refl x⟩, ?_, ?_⟩
  · rintro x y ⟨h1, h2⟩
    exact ⟨r_symm h1, s_symm h2⟩
  · rintro x y z ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨r_trans h1 h3, s_trans h2 h4⟩

theorem star_single {α : Type} (T1 : RelP α) {x y : α} (h : T1 x y) : StarR T1 x y :=
by
  exact StarR.step h (StarR.refl y)

end Section01

namespace Section02

def RelP (α : Type) := α → α → Prop
def ReflR {α : Type} (R : RelP α) : Prop := ∀ x, R x x
def SymmR {α : Type} (R : RelP α) : Prop := ∀ {x y}, R x y → R y x
def TransR {α : Type} (R : RelP α) : Prop := ∀ {x y z}, R x y → R y z → R x z
def EquivR {α : Type} (R : RelP α) : Prop := ReflR R ∧ SymmR R ∧ TransR R

inductive StarR {α : Type} (R : RelP α) : α → α → Prop where
  | refl (x : α) : StarR R x x
  | step {x y z : α} : R x y → StarR R y z → StarR R x z
def ConvR {α : Type} (R : RelP α) : RelP α := fun x y => R y x
def CompR {α : Type} (R S : RelP α) : RelP α := fun x z => ∃ y, R x y ∧ S y z

theorem conv_comp_rev {α : Type} (R S : RelP α) (x z : α) : ConvR (CompR R S) x z ↔ CompR (ConvR S) (ConvR R) x z :=
by
  constructor
  · rintro ⟨y, hry, hsz⟩
    exact ⟨y, hsz, hry⟩
  · rintro ⟨y, hsz, hry⟩
    exact ⟨y, hry, hsz⟩

theorem comp_assoc {α : Type} (R S T : RelP α) (x w : α) : CompR (CompR R S) T x w ↔ CompR R (CompR S T) x w :=
by
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, ⟨z, hyz, hzw⟩⟩
  · rintro ⟨y, hxy, ⟨z, hyz, hzw⟩⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

theorem symm_union_conv {α : Type} (R : RelP α) : SymmR (fun x y => R x y ∨ ConvR R x y) :=
by
  rintro x y (h1 | h2)
  · exact Or.inr h1
  · exact Or.inl h2

theorem conv_invol {α : Type} (R : RelP α) (x y : α) : ConvR (ConvR R) x y ↔ R x y :=
by
  exact Iff.rfl

theorem symm_inter_conv {α : Type} (R : RelP α) : SymmR (fun x y => R x y ∧ ConvR R x y) :=
by
  rintro x y ⟨h1, h2⟩
  exact ⟨h2, h1⟩

end Section02

namespace Section03

inductive StarStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : StarStep R x x
  | step {x y z : α} : R x y → StarStep R y z → StarStep R x z

inductive PlusStep {α : Type} (R : α → α → Prop) : α → α → Prop where
  | single {x y : α} : R x y → PlusStep R x y
  | step {x y z : α} : R x y → PlusStep R y z → PlusStep R x z

def Simulates {α β : Type} (R : α → α → Prop) (T : β → β → Prop) (sim : α → β → Prop) : Prop :=
  ∀ {a1 a2 b1}, sim a1 b1 → R a1 a2 → ∃ b2, T b1 b2 ∧ sim a2 b2

theorem plus_trans {α : Type} (R : α → α → Prop) {x y z : α} (h1 : PlusStep R x y) (h2 : PlusStep R y z) : PlusStep R x z :=
by
  induction h1 with
  | single hxy => exact PlusStep.step hxy h2
  | step hxy _ ih => exact PlusStep.step hxy (ih h2)

theorem plus_to_star {α : Type} (R : α → α → Prop) {x y : α} (hp : PlusStep R x y) : StarStep R x y :=
by
  induction hp with
  | single hxy => exact StarStep.step hxy (StarStep.refl _)
  | step hxy _ ih => exact StarStep.step hxy ih

theorem deterministic_confluence_step {α : Type} (R : α → α → Prop) (hdet : ∀ {x y1 y2}, R x y1 → R x y2 → y1 = y2) {a b1 b2 : α} (h1 : StarStep R a b1) (h2 : StarStep R a b2) (hnf1 : ∀ z, ¬ R b1 z) (hnf2 : ∀ z, ¬ R b2 z) : b1 = b2 :=
by
  induction h1 with
  | refl a =>
    cases h2 with
    | refl => rfl
    | step hr2 _ => exact False.elim (hnf1 _ hr2)
  | step hr1 _ ih =>
    cases h2 with
    | refl => exact False.elim (hnf2 _ hr1)
    | step hr2 h2_rest =>
      have heq := hdet hr1 hr2
      subst heq
      exact ih h2_rest hnf1

theorem simulation_star_lift {α β : Type} (R : α → α → Prop) (T : β → β → Prop) (sim : α → β → Prop) (hsim : Simulates R T sim) {a1 a2 : α} {b1 : β} (hab : sim a1 b1) (hsteps : StarStep R a1 a2) : ∃ b2, StarStep T b1 b2 ∧ sim a2 b2 :=
by
  induction hsteps generalizing b1 with
  | refl a => exact ⟨b1, StarStep.refl b1, hab⟩
  | step hr _ ih =>
    rcases hsim hab hr with ⟨b_mid, ht1, hsim_mid⟩
    rcases ih hsim_mid with ⟨b2, ht_rest, hsim2⟩
    exact ⟨b2, StarStep.step ht1 ht_rest, hsim2⟩

theorem step_star_to_plus {α : Type} (R : α → α → Prop) {x y z : α} (h1 : R x y) (h2 : StarStep R y z) : PlusStep R x z :=
by
  induction h2 generalizing x with
  | refl _ => exact PlusStep.single h1
  | step hyw _ ih => exact PlusStep.step h1 (ih hyw)

end Section03

namespace Section04

def SetP (α : Type) := α → Prop
def SubP {α : Type} (A B : SetP α) : Prop := ∀ x, A x → B x
def InterP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∧ B x
def UnionP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∨ B x
def ComplP {α : Type} (A : SetP α) : SetP α := fun x => ¬ A x
def DiffP {α : Type} (A B : SetP α) : SetP α := fun x => A x ∧ ¬ B x
def PreimgP {α β : Type} (f : α → β) (B : SetP β) : SetP α := fun x => B (f x)
def ImgP {α β : Type} (f : α → β) (A : SetP α) : SetP β := fun y => ∃ x, A x ∧ f x = y

theorem img_inter_sub {α β : Type} (f : α → β) (S1 S2 : SetP α) : SubP (ImgP f (InterP S1 S2)) (InterP (ImgP f S1) (ImgP f S2)) :=
by
  rintro y ⟨x, ⟨ha, hb⟩, hfx⟩
  exact ⟨⟨x, ha, hfx⟩, ⟨x, hb, hfx⟩⟩

theorem img_union {α β : Type} (f : α → β) (A B : SetP α) : ∀ y, ImgP f (UnionP A B) y ↔ UnionP (ImgP f A) (ImgP f B) y :=
by
  intro y
  constructor
  · rintro ⟨x, ha | hb, hfx⟩
    · exact Or.inl ⟨x, ha, hfx⟩
    · exact Or.inr ⟨x, hb, hfx⟩
  · rintro (⟨x, ha, hfx⟩ | ⟨x, hb, hfx⟩)
    · exact ⟨x, Or.inl ha, hfx⟩
    · exact ⟨x, Or.inr hb, hfx⟩

theorem set_diff_inter_compl {α : Type} (E F G : SetP α) : ∀ x, DiffP E (UnionP F G) x ↔ InterP (DiffP E F) (DiffP E G) x :=
by
  intro x
  constructor
  · rintro ⟨ha, hnbc⟩
    exact ⟨⟨ha, fun hb => hnbc (Or.inl hb)⟩, ⟨ha, fun hc => hnbc (Or.inr hc)⟩⟩
  · rintro ⟨⟨ha, hnb⟩, ⟨_, hnc⟩⟩
    refine ⟨ha, ?_⟩
    rintro (hb | hc)
    · exact hnb hb
    · exact hnc hc

theorem set_union_distrib_inter {α : Type} (E F G : SetP α) : ∀ x, UnionP E (InterP F G) x ↔ InterP (UnionP E F) (UnionP E G) x :=
by
  intro x
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · exact ⟨Or.inl ha, Or.inl ha⟩
    · exact ⟨Or.inr hb, Or.inr hc⟩
  · rintro ⟨ha | hb, ha' | hc⟩
    · exact Or.inl ha
    · exact Or.inl ha
    · exact Or.inl ha'
    · exact Or.inr ⟨hb, hc⟩

theorem set_inter_distrib_union {α : Type} (A1 A2 A3 : SetP α) : ∀ x, InterP A1 (UnionP A2 A3) x ↔ UnionP (InterP A1 A2) (InterP A1 A3) x :=
by
  intro x
  constructor
  · rintro ⟨ha, hb | hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hc⟩

theorem preimg_inter {α β : Type} (f : α → β) (S T : SetP β) : ∀ x, PreimgP f (InterP S T) x ↔ InterP (PreimgP f S) (PreimgP f T) x :=
by
  intro x
  exact Iff.rfl

theorem img_inter_eq_of_inj {α β : Type} (f : α → β) (hinj : ∀ x1 x2, f x1 = f x2 → x1 = x2) (U1 U2 : SetP α) : SubP (InterP (ImgP f U1) (ImgP f U2)) (ImgP f (InterP U1 U2)) :=
by
  rintro y ⟨⟨x1, ha, hx1⟩, ⟨x2, hb, hx2⟩⟩
  have heq : x1 = x2 := hinj x1 x2 (hx1.trans hx2.symm)
  subst heq
  exact ⟨x1, ⟨ha, hb⟩, hx1⟩

theorem set_demorgan_union {α : Type} (E F : SetP α) : ∀ x, ComplP (UnionP E F) x ↔ InterP (ComplP E) (ComplP F) x :=
by
  intro x
  constructor
  · intro h
    exact ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩
  · rintro ⟨hna, hnb⟩ (ha | hb)
    · exact hna ha
    · exact hnb hb

theorem img_preimg_galois {α β : Type} (f : α → β) (S : SetP α) (T : SetP β) : SubP (ImgP f S) T ↔ SubP S (PreimgP f T) :=
by
  constructor
  · intro h x hx
    exact h (f x) ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h x hx

theorem set_demorgan_inter_classical {α : Type} (A1 A2 : SetP α) : ∀ x, ComplP (InterP A1 A2) x ↔ UnionP (ComplP A1) (ComplP A2) x :=
by
  intro x
  constructor
  · intro h
    cases Classical.em (A1 x) with
    | inl ha => exact Or.inr (fun hb => h ⟨ha, hb⟩)
    | inr hna => exact Or.inl hna
  · rintro (hna | hnb) ⟨ha, hb⟩
    · exact hna ha
    · exact hnb hb

theorem set_sub_trans {α : Type} (P Q R : SetP α) (h1 : SubP P Q) (h2 : SubP Q R) : SubP P R :=
by
  intro x hx
  exact h2 x (h1 x hx)

end Section04

end PureLean.RelationsSets
