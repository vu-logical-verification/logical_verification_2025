/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Preface

## Proof Assistants

Proof assistants (also called interactive theorem provers)

* check and help develop formal proofs;
* can be used to prove big theorems, not only logic puzzles;
* can be tedious to use;
* are highly addictive (think video games).

A selection of proof assistants, classified by logical foundations:

* set theory: Isabelle/ZF, Metamath, Mizar;
* simple type theory: HOL4, HOL Light, Isabelle/HOL;
* **dependent type theory**: Agda, Coq, **Lean**, Matita, PVS.


## Success Stories

Mathematics:

* the four-color theorem (in Coq);
* the Kepler conjecture (in HOL Light and Isabelle/HOL);
* the definition of perfectoid spaces (in Lean).

Computer science:

* hardware;
* operating systems;
* programming language theory;
* compilers;
* security.


## Lean

Lean is a proof assistant developed primarily by Leonardo de Moura (Amazon Web
Services) since 2012.

Its mathematical library, `mathlib`, is developed by a large community of
contributors.

We use the community version of Lean 4. We use its basic libraries, `mathlib4`,
and `LoVelib`, among others. Lean is a research project.

Strengths:

* highly expressive logic based on a dependent type theory called the
  **calculus of inductive constructions**;
* extended with classical axioms and quotient types;
* metaprogramming framework;
* modern user interface;
* documentation;
* open source;
* endless source of puns (Lean Forward, Lean Together, Boolean, …).


## Our Goal

We want you to

* master fundamental theory and techniques in interactive theorem proving;
* get familiarized with some application areas;
* develop some practical skills you can apply on a larger project (as a hobby,
  for an MSc or PhD, or in industry);
* feel ready to move to another proof assistant and apply what you have learned;
* understand the domain well enough to start reading scientific papers.

This course is neither a pure logical foundations course nor a Lean tutorial.
Lean is our means, not an end of itself.


# LoVe Demo 1: Types and Terms

We start our journey by studying the basics of Lean, starting with terms
(expressions) and their types. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## A View of Lean

In a first approximation:

    Lean = functional programming + logic

In today's lecture, we cover the syntax of types and terms, which are similar to
those of the simply typed λ-calculus or typed functional programming languages
(ML, OCaml, Haskell).


## Types

Types `σ`, `τ`, `υ`:

* type variables `α`;
* basic types `T`;
* complex types `T σ1 … σN`.

Some type constructors `T` are written infix, e.g., `→` (function type).

The function arrow is right-associative:
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`.

Polymorphic types are also possible. In Lean, the type variables must be bound
using `∀`, e.g., `∀α, α → α`.


## Terms

Terms `t`, `u`:

* constants `c`;
* variables `x`;
* applications `t u`;
* anonymous functions `fun x ↦ t` (also called λ-expressions).

__Currying__: functions can be

* fully applied (e.g., `f x y z` if `f` can take at most 3 arguments);
* partially applied (e.g., `f x y`, `f x`);
* left unapplied (e.g., `f`).

Application is left-associative: `f x y z` = `((f x) y) z`.

`#check` reports the type of its argument.
`#print` prints the definition of its argument
-/

#check ℕ
#print Nat
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))


/- `opaque` defines an arbitrary constant of the specified type. -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x

end LoVe
