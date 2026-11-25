/-!
# PureLean.LogicFunctions

Constructive & Classical Logic, Cantor Diagonalization, Lawvere Fixed Points, Function Bijections, and Option Monads.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.LogicFunctions

namespace Section01

def SurjectiveFn {α β : Type} (f : α → β) : Prop := ∀ b : β, ∃ a : α, f a = b
def InjectiveFn {α β : Type} (f : α → β) : Prop := ∀ ⦃a1 a2 : α⦄, f a1 = f a2 → a1 = a2

def optMap {α β : Type} (f : α → β) : Option α → Option β
  | none => none
  | some x => some (f x)

def optBind {α β : Type} : Option α → (α → Option β) → Option β
  | none, _ => none
  | some x, f => f x

theorem drinker_paradox_classical {α : Type} (x0 : α) (D : α → Prop) : ∃ x : α, D x → ∀ y : α, D y :=
by
  cases Classical.em (∀ y : α, D y) with
  | inl hall => exact ⟨x0, fun _ => hall⟩
  | inr hnall =>
    have hex : ∃ x : α, ¬ D x := by
      apply Classical.byContradiction
      intro hno
      apply hnall
      intro y
      cases Classical.em (D y) with
      | inl hdy => exact hdy
      | inr hndy => exact False.elim (hno ⟨y, hndy⟩)
    rcases hex with ⟨x, hnx⟩
    exact ⟨x, fun hdx => False.elim (hnx hdx)⟩

theorem prod_swap_bij (α β : Type) : InjectiveFn (fun p : α × β => (p.2, p.1)) ∧ SurjectiveFn (fun p : α × β => (p.2, p.1)) :=
by
  constructor
  · rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    cases h
    rfl
  · rintro ⟨b, a⟩
    exact ⟨(a, b), rfl⟩

theorem optBind_right_id {α : Type} (mx : Option α) : optBind mx some = mx :=
by
  cases mx <;> rfl

theorem lawvere_prop_fixpoint (α : Type) (f : α → (α → Prop)) (hsurj : SurjectiveFn f) (g : Prop → Prop) : ∃ P : Prop, g P ↔ P :=
by
  rcases hsurj (fun x => g (f x x)) with ⟨a, ha⟩
  have heq : f a a = g (f a a) := congrFun ha a
  refine ⟨f a a, ?_⟩
  rw [← heq]

theorem optMap_eq_bind {α β : Type} (f : α → β) (mx : Option α) : optMap f mx = optBind mx (fun x => some (f x)) :=
by
  cases mx <;> rfl

theorem cantor_no_surj (α : Type) (f : α → (α → Prop)) : ¬ SurjectiveFn f :=
by
  intro hsurj
  rcases hsurj (fun x => ¬ f x x) with ⟨a, ha⟩
  have hdiag : f a a = (¬ f a a) := congrFun ha a
  have hna : ¬ f a a := by
    intro hfaa
    have hn : ¬ f a a := Eq.mp hdiag hfaa
    exact hn hfaa
  exact hna (Eq.mpr hdiag hna)

theorem barber_irreflexive {α : Type} (shaves : α → α → Prop) : ¬ ∃ b : α, ∀ x : α, shaves b x ↔ ¬ shaves x x :=
by
  rintro ⟨b, hb⟩
  have hbb := hb b
  have hnb : ¬ shaves b b := fun h => hbb.mp h h
  exact hnb (hbb.mpr hnb)

theorem optBind_assoc {α β γ : Type} (mx : Option α) (f : α → Option β) (g : β → Option γ) : optBind (optBind mx f) g = optBind mx (fun x => optBind (f x) g) :=
by
  cases mx <;> rfl

end Section01

namespace Section02

def InjFn {α β : Type} (f : α → β) : Prop := ∀ ⦃x y : α⦄, f x = f y → x = y
def SurjFn {α β : Type} (f : α → β) : Prop := ∀ y : β, ∃ x : α, f x = y
def BijFn {α β : Type} (f : α → β) : Prop := InjFn f ∧ SurjFn f
def LeftInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ x : α, g (f x) = x
def RightInvFn {α β : Type} (g : β → α) (f : α → β) : Prop := ∀ y : β, f (g y) = y

def iterFn {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iterFn f n x)

theorem iterFn_add {α : Type} (f : α → α) (m n : Nat) (x : α) : iterFn f (m + n) x = iterFn f m (iterFn f n x) :=
by
  induction m with
  | zero => simp [iterFn]
  | succ k ih =>
    rw [Nat.succ_add, iterFn, iterFn, ih]

theorem iterFn_fixed {α : Type} (f : α → α) (x : α) (hx : f x = x) (n : Nat) : iterFn f n x = x :=
by
  induction n with
  | zero => rfl
  | succ k ih => simp [iterFn, ih, hx]

theorem left_right_inv_eq {α β : Type} (f : α → β) (g1 g2 : β → α) (hl : LeftInvFn g1 f) (hr : RightInvFn g2 f) : ∀ y, g1 y = g2 y :=
by
  intro y
  calc g1 y = g1 (f (g2 y)) := by rw [hr y]
    _ = g2 y := by rw [hl (g2 y)]

theorem surj_of_right_inv {α β : Type} (f : α → β) (g : β → α) (h : RightInvFn g f) : SurjFn f :=
by
  intro y
  exact ⟨g y, h y⟩

theorem iterFn_comm_single {α : Type} (f : α → α) (n : Nat) (x : α) : iterFn f n (f x) = f (iterFn f n x) :=
by
  induction n with
  | zero => rfl
  | succ k ih => simp [iterFn, ih]

theorem inj_comp {α β γ : Type} (f : α → β) (g : β → γ) (hf : InjFn f) (hg : InjFn g) : InjFn (fun x => g (f x)) :=
by
  intro x y h
  exact hf (hg h)

theorem iterFn_comm_general {α : Type} (f g : α → α) (hc : ∀ x, f (g x) = g (f x)) (n : Nat) (x : α) : f (iterFn g n x) = iterFn g n (f x) :=
by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [iterFn]
    rw [hc (iterFn g k x), ih]

theorem inj_of_left_inv {α β : Type} (f : α → β) (g : β → α) (h : LeftInvFn g f) : InjFn f :=
by
  intro x y hfx
  have h1 := congrArg g hfx
  rw [h x, h y] at h1
  exact h1

theorem surj_comp {α β γ : Type} (f : α → β) (g : β → γ) (hf : SurjFn f) (hg : SurjFn g) : SurjFn (fun x => g (f x)) :=
by
  intro z
  rcases hg z with ⟨y, rfl⟩
  rcases hf y with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

theorem inj_of_comp_inj {α β γ : Type} (f : α → β) (g : β → γ) (h : InjFn (fun x => g (f x))) : InjFn f :=
by
  intro x y hfx
  exact h (congrArg g hfx)

theorem surj_of_comp_surj {α β γ : Type} (f : α → β) (g : β → γ) (h : SurjFn (fun x => g (f x))) : SurjFn g :=
by
  intro z
  rcases h z with ⟨x, hx⟩
  exact ⟨f x, hx⟩

end Section02

namespace Section03

theorem logic_contrapos_classical (U1 U2 : Prop) : (¬U2 → ¬U1) ↔ (U1 → U2) :=
by
  constructor
  · intro h hp
    cases Classical.em U2 with
    | inl hq => exact hq
    | inr hnq => exact False.elim (h hnq hp)
  · intro h hnq hp
    exact hnq (h hp)

theorem logic_imp_and_iff (P Q R : Prop) : (P → (Q ∧ R)) ↔ ((P → Q) ∧ (P → R)) :=
by
  constructor
  · intro h; exact ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩
  · rintro ⟨hpq, hpr⟩ hp; exact ⟨hpq hp, hpr hp⟩

theorem logic_dneg_map (P Q : Prop) (h : P → Q) : ¬¬P → ¬¬Q :=
by
  intro hnnp hnq
  exact hnnp (fun hp => hnq (h hp))

theorem logic_triple_neg (P : Prop) : ¬¬¬P ↔ ¬P :=
by
  constructor
  · intro hnnnp hp
    exact hnnnp (fun hnp => hnp hp)
  · intro hnp hnnp
    exact hnnp hnp

theorem logic_dneg_em (H1 : Prop) : ¬¬(H1 ∨ ¬H1) :=
by
  intro h
  have hnp : ¬H1 := fun hp => h (Or.inl hp)
  exact h (Or.inr hnp)

theorem logic_peirce (L1 L2 : Prop) : ((L1 → L2) → L1) → L1 :=
by
  intro h
  cases Classical.em L1 with
  | inl hp => exact hp
  | inr hnp => exact h (fun hp => False.elim (hnp hp))

theorem logic_dneg_ap (H1 H2 : Prop) : ¬¬(H1 → H2) → ¬¬H1 → ¬¬H2 :=
by
  intro hnnf hnnp hnq
  apply hnnf
  intro hpq
  apply hnnp
  intro hp
  exact hnq (hpq hp)

theorem quant_not_forall_classical {α : Type} (P : α → Prop) : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) :=
by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hne
    apply h
    intro x
    cases Classical.em (P x) with
    | inl hpx => exact hpx
    | inr hnpx => exact False.elim (hne ⟨x, hnpx⟩)
  · rintro ⟨x, hnpx⟩ hall
    exact hnpx (hall x)

theorem logic_imp_or_classical (P Q R : Prop) : (P → Q ∨ R) ↔ ((P → Q) ∨ (P → R)) :=
by
  constructor
  · intro h
    cases Classical.em P with
    | inl hp =>
      rcases h hp with hq | hr
      · exact Or.inl (fun _ => hq)
      · exact Or.inr (fun _ => hr)
    | inr hnp =>
      exact Or.inl (fun hp => False.elim (hnp hp))
  · rintro (hpq | hpr) hp
    · exact Or.inl (hpq hp)
    · exact Or.inr (hpr hp)

theorem quant_exists_or {α : Type} (P Q : α → Prop) : (∃ x, P x ∨ Q x) ↔ ((∃ x, P x) ∨ (∃ x, Q x)) :=
by
  constructor
  · rintro ⟨x, hp | hq⟩
    · exact Or.inl ⟨x, hp⟩
    · exact Or.inr ⟨x, hq⟩
  · rintro (⟨x, hp⟩ | ⟨x, hq⟩)
    · exact ⟨x, Or.inl hp⟩
    · exact ⟨x, Or.inr hq⟩

theorem quant_not_exists {α : Type} (P : α → Prop) : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) :=
by
  constructor
  · intro h x hx; exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩; exact h x hx

theorem logic_or_imp_iff (M1 M2 M3 : Prop) : ((M1 ∨ M2) → M3) ↔ ((M1 → M3) ∧ (M2 → M3)) :=
by
  constructor
  · intro h; exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · rintro ⟨hpr, hqr⟩ (hp | hq)
    · exact hpr hp
    · exact hqr hq

theorem quant_exists_swap {α β : Type} (R : α → β → Prop) : (∃ x, ∃ y, R x y) ↔ (∃ y, ∃ x, R x y) :=
by
  constructor
  · rintro ⟨x, y, h⟩; exact ⟨y, x, h⟩
  · rintro ⟨y, x, h⟩; exact ⟨x, y, h⟩

theorem quant_forall_and {α : Type} (P Q : α → Prop) : (∀ x, P x ∧ Q x) ↔ ((∀ x, P x) ∧ (∀ x, Q x)) :=
by
  constructor
  · intro h; exact ⟨fun x => (h x).1, fun x => (h x).2⟩
  · rintro ⟨hp, hq⟩ x; exact ⟨hp x, hq x⟩

theorem logic_diamond_imp (Phi Psi Chi Xi : Prop) (h1 : Phi → Psi ∨ Chi) (h2 : Psi → Xi) (h3 : Chi → Xi) : Phi → Xi :=
by
  intro hp
  rcases h1 hp with hq | hr
  · exact h2 hq
  · exact h3 hr

theorem quant_exists_forall_imp {α β : Type} (R : α → β → Prop) : (∃ x, ∀ y, R x y) → (∀ y, ∃ x, R x y) :=
by
  rintro ⟨x, hx⟩ y
  exact ⟨x, hx y⟩

theorem logic_curry_iff (L1 L2 L3 : Prop) : ((L1 ∧ L2) → L3) ↔ (L1 → L2 → L3) :=
by
  constructor
  · intro h hp hq; exact h ⟨hp, hq⟩
  · rintro h ⟨hp, hq⟩; exact h hp hq

end Section03

end PureLean.LogicFunctions
