import LoVe.LoVelib

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace Prac5

def fold_left {α : Type} (f : α → α → α) (i : α) : List α → α
  | [] => i
  | x :: xs => fold_left f (f i x) xs

#print fold_left

def fold_right {α : Type} (f : α → α → α) : List α → α → α
  | [], i => i
  | x :: xs, i => f x (fold_right f xs i)

#eval fold_left Int.add 0 [1, 2, 3]
#eval fold_right Int.add [1, 2, 3] 0

#eval fold_left Int.sub 0 [1, 2, 3]
#eval fold_right Int.sub [1, 2, 3] 0

def Commutative {α : Type} (f : α → α → α) : Prop :=
  forall x y, f x y = f y x

def Associative {α : Type} (f : α → α → α) : Prop :=
  forall x y z, f x (f y z) = f (f x y) z

/-
  Prove the following lemmas about folds,
  using the Associative and/or Commutative definitions.
  A hint for the first proof:

  The `revert` keyword allows you to effectively 'undo' an intro.
  Check the example out below.

  If you do induction with y in ∀, then the induction hypothesis
  may also include this ∀, leading to a more general hypothesis...
-/

lemma revert_example {α : Type} (y : ℕ) (f : ℕ → ℕ) : f y = f (y+1) :=
  by
  -- goal: α, y, f ⊢ f y = f (y + 1)
  revert y
  -- goal: α, f ⊢ ∀ (y : ℕ), f y = f (y + 1)
  -- (Do NOT try to complete this proof.)
  sorry

lemma fold_left_app {α : Type} (f : α → α → α) (x i : α) (xs : List α) :
  Associative f →
  fold_left f (f x i) xs = f x (fold_left f i xs) :=
  by sorry

lemma fold_left_right_eq {α : Type} (f : α → α → α) :
  Commutative f → Associative f →
  ∀ (i : α) (xs : List α),
    fold_left f i xs = fold_right f xs i :=
  by sorry


end Prac5

end LoVe
