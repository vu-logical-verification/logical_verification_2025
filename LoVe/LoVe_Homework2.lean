/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6 (20 points): Functional Programming and Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe



/- ## Question 1 (6 points): Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 1.1 (3 points). Prove the following theorem, discovered by Carl Friedrich
Gauss as a pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic might be useful to reason about
  addition. -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1) := sorry


/- 1.2 (3 points). Prove the following property of `sumUpToOfFun`. -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n := sorry

/- ## Question 2 (4 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive Even : ℕ → Prop
  | zero            : Even 0
  | add_two (k : ℕ) : Even k → Even (k + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `Even`,
and should not rely on `Even`. -/

inductive Odd : ℕ → Prop
-- supply the missing cases here

/- 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

theorem Odd_3 :
    Odd 3 :=
  sorry

theorem Odd_5 :
    Odd 5 :=
  sorry

/- 2.3 (2 point). Prove the following theorems by rule induction: -/

theorem Even_Odd {n : ℕ} (heven : Even n) :
    Odd (n + 1) :=
  sorry

theorem Even_Not_Odd {n : ℕ} (heven : Even n) :
    ¬ Odd n :=
  sorry

/- ## Question 3 (4 points): Reflexive Transitive Closure^2 -/

/- Consider the following inductive definition of the
   reflexive transitive closure of a relation `R`,
   modeled as a binary predicate `Star' R`. -/

inductive Star' {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (a : α)      : Star' R a a
  | chain (a b c : α) : Star' R a b → R b c → Star' R a c

/- We proved the following two properties in the lecture: -/

lemma Star.closure {α : Type} (R : α → α → Prop) (a b : α) :
    R a b → Star' R a b :=
    by
      intro hab
      apply Star'.chain a a b
      {exact Star'.refl a}
      {exact hab}

theorem startransitive {α : Type} (R : α → α → Prop) (a b c: α) :
  Star' R a b → Star' R b c → Star' R a c :=
    by
      intro sab sbc
      induction sbc with
      | refl  => apply sab
      | chain a' b' hsrba hra'b' ih =>
        apply Star'.chain
        {exact ih}
        {exact hra'b'}


/- Prove that `Star' (Star' R)` is the same relation as `Star' R`.
   You may use the above two lemmas. -/

lemma Star.Star_Iff_Star {α : Type} (R : α → α → Prop) (a b : α) :
    Star' (Star' R) a b ↔ Star' R a b :=
  sorry


/- ## Question 4 (6 points): Sets -/

/- One approach to implementing sets that are extensional
   (that is, two sets are equal iff they have the same elements)
   in proof assistants is to maintain a strict order on the elements. -/


   -- We will use a comparison type together with two functions
   -- compare and compare_nat. We need them, instead of just using <, since
   -- we use the Option ℕ type in our set definition.
  inductive Comparison : Type
  | lt : Comparison
  | eq : Comparison
  | gt : Comparison

  open Comparison

  /- We will be working with sets of natural numbers. -/

  def compare_nat : ℕ → ℕ → Comparison
  | Nat.zero, Nat.zero => eq
  | Nat.zero, Nat.succ _ => lt
  | Nat.succ _, Nat.zero => gt
  | Nat.succ a, Nat.succ b => compare_nat a b

  /- An `Option α` type has either the form `some a` for a value of type α or
  it has the form `none`. -/
  -- inductive Option.{u} : Type u → Type u
  --   | Option.none : {α : Type u} → Option α
  --   | Option.some : {α : Type u} → α → Option α


  def compare : Option ℕ → Option ℕ → Comparison
  | none, none => eq
  | none, some _ => gt
  | some _, none => lt
  | some a, some b => compare_nat a b




  /- This lemma might make things easier-/
  lemma compare_nat_compares (a b : ℕ) : compare_nat a b = lt ↔ a < b := by
    induction a generalizing b with
      | zero =>
          cases b with
        | zero => simp [compare_nat]
        | succ b' => simp [compare_nat]
      | succ a ih =>
        cases b with
          | zero => simp [compare_nat]
          | succ b' =>
          simp [compare_nat]
          rw [ih b']




  /- A term of type `SetAbove (some a)` type is a set whose smallest element is `a`;
  a term of type `SetAbove none` is the empty set.
  -- for example: ∅ : SetAbove none, {1,2,3} : SetAbove (some 1) -/



  /-
  The definition of SetAbove is similar to the definition of a list
  Similar to the list constructor List.cons, scons also takes a next element e : ℕ and a set s : SetAbove a as arguments
  Unlike the list constructor, the scons also takes as argument a proof that e is less than a, since we ensure uniqueness by order
  -/

  inductive SetAbove : Option ℕ → Type
  | snil : SetAbove none
  | scons (a : ℕ) (k : Option ℕ): compare (some a) k = lt → SetAbove k → SetAbove (some a)


  /- 4.1 (1 point) Complete the definition empty that returns the empty set. -/
  def empty : SetAbove none := sorry


  /- 4.2 (1 point) Complete the definition of a singleton set. -/
  -- For each number a, singleton a should return the set {a}, i.e. a->∅.
  def singleton (a : ℕ) : SetAbove (some a) := sorry

  /- 4.3 (2 point) Complete the definition of a membership predicate that checks whether a
  number a is a member of a set
  -/
  def mem (a : ℕ) {k : Option ℕ} : SetAbove k → Bool := sorry

  /- 4.4 (2 point) Show that an element smaller than the smallest element of the set
  can (unsurprisingly) never belong to the set. -/
  #check compare_nat_compares

  lemma mem_lt_key_false (a : Nat) (k : Option Nat) (m : SetAbove k) :
  compare (some a) k = lt →
  mem a m = false := sorry



  end LoVe
