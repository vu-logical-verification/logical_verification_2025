/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib

-- defining terms
def addone : ℕ → ℕ :=
  λ x ↦ x + 1

def addnumbers (a : ℕ) : ℕ → ℕ :=
  λ b ↦ a + b

def addnumbers' : ℕ → ℕ → ℕ :=
  λ a b ↦ a + b

#check addnumbers
#check addnumbers'


def nodef : ℕ := sorry
opaque nodef' : ℕ

-- defining types
opaque T : Type
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat'

-- using inductive types
def one' : Nat' := Nat'.succ Nat'.zero
def add' : Nat' → Nat' → Nat'
  | a, Nat'.zero => a
  | a, Nat'.succ b => Nat'.succ (add' a b)

-- polymorphic types
#check List
#check List ℕ


-- def addone : ℕ → ℕ := λ x ↦ x + 1
theorem simpletheorem : ∀a : Prop , a → a := λ (a: Prop) (ha : a) ↦ ha
theorem simpletheorem' (a : Prop) :  a → a := λ (ha : a) ↦ ha
theorem simpletheorem'' : (a : Prop) → a → a := λ (a: Prop) (ha : a) ↦ ha

#check simpletheorem
#check simpletheorem'
#check simpletheorem''

-- tactics

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

#check fst_of_two_props
#print fst_of_two_props



theorem sometheorem (a b : Prop) : a -> (a -> b) -> b := sorry

theorem multiplegoals (a b c d : Prop) (ha : a) (hb : b) (hc : c) (hbcde : a → b → c → d) : d := sorry


#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- Elimination rules: -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- Definition of `¬` and related theorems: -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- There are no explicit rules for `Not` (`¬`) since `¬ p` is defined as
`p → False`. -/


theorem And_swap (a b : Prop) : a ∧ b → b ∧ a := sorry

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a := sorry

--  ¬a is defined as a → False
theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a := sorry


theorem And_swap' (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right hab
    apply And.left hab





-- theorem And_swap (a b : Prop) :
--     a ∧ b → b ∧ a :=
--   by
--     intro hab
--     apply And.intro
--     apply And.right hab
--     apply And.left hab

/- The above proof step by step:

* Assume we know `a ∧ b`.
* The goal is `b ∧ a`.
* Show `b`, which we can if we can show a conjunction with `b` on the right.
* We can, we already have `a ∧ b`.
* Show `a`, which we can if we can show a conjunction with `a` on the left.
* We can, we already have `a ∧ b`.

The `{ … }` combinator focuses on a specific subgoal. The tactic inside must
fully prove it. In the proof below, `{ … }` is used for each of the two subgoals
to give more structure to the proof. -/

-- theorem And_swap_braces :
--     ∀a b : Prop, a ∧ b → b ∧ a :=
--   by
--     intro a b hab
--     apply And.intro
--     { exact And.right hab }
--     { exact And.left hab }

/- Notice above how we pass the hypothesis `hab` directly to the theorems
`And.right` and `And.left`, instead of waiting for the theorems' assumptions to
appear as new subgoals. This is a small forward step in an otherwise backward
proof. -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro' (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha


/- ## Reasoning about Equality -/

theorem rfltheorem : 1 = 1 :=
  by
    apply rfl



#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- The above rules can be used directly: -/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

/- `rw` applies a single equation as a left-to-right rewrite rule, once. To
apply an equation right-to-left, prefix its name with `←`. -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab]
    rw [hcb]

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]


/- ## Proofs by Mathematical Induction

`induction` performs induction on the specified variable. It gives rise to one
named subgoal per constructor. -/

-- def add' : Nat' → Nat' → Nat'
--   | a, Nat'.zero => a
--   | a, Nat'.succ b => Nat'.succ (add' a b)


theorem add_zero' (n : Nat') :
    add' Nat'.zero n = n :=
  by
    induction n with
      | zero =>
        simp [add']
      | succ n' ih=>
        simp [add',ih]


theorem add_succ (m n : Nat') :
    add' (Nat'.succ m) n = Nat'.succ (add' m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add', ih]

theorem add_comm' (m n : Nat') :
    add' m n = add' n m :=
  by
    induction n with
    | zero       => simp [add', add_zero']
    | succ n' ih => simp [add', add_succ, ih]

-- We can choose where to apply a rw operation
