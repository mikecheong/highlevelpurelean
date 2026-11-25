/-!
# PureLean.InductiveCompilers

Inductive Data Structures, Binary Tree Mirrors/Traversals, Tail-Recursive Accumulators, and Stack-VM Compilers.
All declarations and proofs use pure Lean 4 (zero Mathlib imports).
-/

namespace PureLean.InductiveCompilers

namespace Section01

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
  | BTree.node l v r => BTree.node (mapT f l) (f v) (mapT f r)

theorem mapT_id {α : Type} (t : BTree α) : mapT (fun x => x) t = t :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mapT, ihl, ihr]

theorem mirrorT_mapT {α β : Type} (f : α → β) (t : BTree α) : mirrorT (mapT f t) = mapT f (mirrorT t) :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mirrorT, mapT, ihl, ihr]

theorem mirrorT_invol {α : Type} (t : BTree α) : mirrorT (mirrorT t) = t :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mirrorT, ihl, ihr]

theorem sizeT_mapT {α β : Type} (f : α → β) (t : BTree α) : sizeT (mapT f t) = sizeT t :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mapT, sizeT, ihl, ihr]

theorem mapT_comp {α β γ : Type} (f : α → β) (g : β → γ) (t : BTree α) : mapT g (mapT f t) = mapT (fun x => g (f x)) t :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mapT, ihl, ihr]

theorem sizeT_mirrorT {α : Type} (t : BTree α) : sizeT (mirrorT t) = sizeT t :=
by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp [mirrorT, sizeT, ihl, ihr]
    omega

end Section01

namespace Section02

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
  | x :: xs => f x (foldrL f z xs)

theorem revAcc_append_acc {α : Type} (xs acc : List α) : revAcc xs acc = revAcc xs [] ++ acc :=
by
  induction xs generalizing acc with
  | nil => simp [revAcc]
  | cons x tl ih =>
    simp only [revAcc]
    rw [ih (x :: acc), ih [x], List.append_assoc]
    rfl

theorem filterL_idem {α : Type} (p : α → Bool) (xs : List α) : filterL p (filterL p xs) = filterL p xs :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [filterL]
    cases hp : p x with
    | false => exact ih
    | true => simp [filterL, hp, ih]

theorem sumAcc_eq_add_sum (xs : List Nat) (acc : Nat) : sumAcc xs acc = acc + sumL2 xs :=
by
  induction xs generalizing acc with
  | nil => simp [sumAcc, sumL2]
  | cons x tl ih =>
    simp [sumAcc, sumL2, ih (acc + x), Nat.add_assoc]

theorem foldrL_append {α β : Type} (f : α → β → β) (z : β) (xs ys : List α) : foldrL f z (xs ++ ys) = foldrL f (foldrL f z ys) xs :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [foldrL, ih]

theorem filterL_append {α : Type} (p : α → Bool) (xs ys : List α) : filterL p (xs ++ ys) = filterL p xs ++ filterL p ys :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    simp only [List.cons_append, filterL]
    cases p x <;> simp [ih]

theorem sumAcc_zero_correct (xs : List Nat) : sumAcc xs 0 = sumL2 xs :=
by
  have haux : ∀ (ys : List Nat) (acc : Nat), sumAcc ys acc = acc + sumL2 ys := by
    intro ys
    induction ys with
    | nil => intro acc; simp [sumAcc, sumL2]
    | cons y tl ih => intro acc; simp [sumAcc, sumL2, ih (acc + y), Nat.add_assoc]
  simpa using haux xs 0

end Section02

namespace Section03

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
  | x :: xs => x + sumL xs

theorem mapL_comp {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) : mapL g (mapL f xs) = mapL (fun x => g (f x)) xs :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [mapL, ih]

theorem length_snocL {α : Type} (xs : List α) (a : α) : (snocL xs a).length = xs.length + 1 :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [snocL, ih]

theorem sumL_snocL (xs : List Nat) (a : Nat) : sumL (snocL xs a) = sumL xs + a :=
by
  induction xs with
  | nil => simp [snocL, sumL]
  | cons x tl ih => simp [snocL, sumL, ih, Nat.add_assoc]

theorem revL_snocL {α : Type} (xs : List α) (a : α) : revL (snocL xs a) = a :: revL xs :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [snocL, revL, ih]

theorem length_revL {α : Type} (xs : List α) : (revL xs).length = xs.length :=
by
  have hsnoc : ∀ (ys : List α) (a : α), (snocL ys a).length = ys.length + 1 := by
    intro ys a
    induction ys with
    | nil => rfl
    | cons y tl ih => simp [snocL, ih]
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [revL, hsnoc, ih]

theorem revL_involutive {α : Type} (xs : List α) : revL (revL xs) = xs :=
by
  have h : ∀ (ys : List α) (a : α), revL (snocL ys a) = a :: revL ys := by
    intro ys a
    induction ys with
    | nil => rfl
    | cons y tl ih => simp [snocL, revL, ih]
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [revL, h, ih]

theorem mapL_id {α : Type} (xs : List α) : mapL (fun x => x) xs = xs :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [mapL, ih]

theorem snocL_eq_append {α : Type} (xs : List α) (a : α) : snocL xs a = xs ++ [a] :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [snocL, ih]

theorem sumL_append (xs ys : List Nat) : sumL (xs ++ ys) = sumL xs + sumL ys :=
by
  induction xs with
  | nil => simp [sumL]
  | cons x tl ih =>
    simp [sumL, ih, Nat.add_assoc]

theorem mapL_snocL {α β : Type} (f : α → β) (xs : List α) (a : α) : mapL f (snocL xs a) = snocL (mapL f xs) (f a) :=
by
  induction xs with
  | nil => rfl
  | cons x tl ih => simp [snocL, mapL, ih]

end Section03

namespace Section04

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
  | FullTree.fork l r => FullTree.fork (flipFT r) (flipFT l)

theorem fulltree_leaves_eq_forks_succ {α : Type} (t : FullTree α) : leavesFT t = forksFT t + 1 :=
by
  induction t with
  | tip _ => rfl
  | fork l r ihl ihr =>
    simp [leavesFT, forksFT, ihl, ihr]
    omega

theorem leavesFT_flipFT {α : Type} (t : FullTree α) : leavesFT (flipFT t) = leavesFT t :=
by
  induction t with
  | tip _ => rfl
  | fork l r ihl ihr => simp [flipFT, leavesFT, ihl, ihr]; omega

theorem flipFT_invol {α : Type} (t : FullTree α) : flipFT (flipFT t) = t :=
by
  induction t with
  | tip _ => rfl
  | fork l r ihl ihr => simp [flipFT, ihl, ihr]

end Section04

namespace Section05

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
  | AddExpr.add e1 e2 => compileAdd e1 ++ compileAdd e2 ++ [VMInstr.addTop]

theorem compileAdd_correct (e : AddExpr) (stk : List Nat) : runVM (compileAdd e) stk = evalAdd e :: stk :=
by
  have hrun : ∀ (c1 c2 : List VMInstr) (s : List Nat), runVM (c1 ++ c2) s = runVM c2 (runVM c1 s) := by
    intro c1 c2
    induction c1 with
    | nil => intro s; rfl
    | cons instr rest ih =>
      intro s
      cases instr with
      | push n => exact ih (n :: s)
      | addTop =>
        rcases s with _ | ⟨b, _ | ⟨a, s'⟩⟩
        · exact ih []
        · exact ih [b]
        · exact ih ((a + b) :: s')
  induction e generalizing stk with
  | lit n => rfl
  | add e1 e2 ih1 ih2 =>
    simp only [compileAdd, evalAdd]
    rw [List.append_assoc, hrun, ih1, hrun, ih2]
    rfl

theorem vm_run_append (c1 c2 : List VMInstr) (stk : List Nat) : runVM (c1 ++ c2) stk = runVM c2 (runVM c1 stk) :=
by
  induction c1 generalizing stk with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | push n => exact ih (n :: stk)
    | addTop =>
      rcases stk with _ | ⟨b, _ | ⟨a, s⟩⟩
      · exact ih []
      · exact ih [b]
      · exact ih ((a + b) :: s)

end Section05

namespace Section06

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
  | PureExpr.mul e1 e2 => PureExpr.mul (optZeroExpr e1) (optZeroExpr e2)

theorem eval_swapAddExpr (env : Nat → Nat) (e : PureExpr) : evalExpr env (swapAddExpr e) = evalExpr env e :=
by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | add e1 e2 ih1 ih2 => simp [swapAddExpr, evalExpr, ih1, ih2, Nat.add_comm]
  | mul e1 e2 ih1 ih2 => simp [swapAddExpr, evalExpr, ih1, ih2]

end Section06

end PureLean.InductiveCompilers
