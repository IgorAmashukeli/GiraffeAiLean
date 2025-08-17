/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

namespace Section3sheet1

/-!

# Functions in Lean.

In this sheet we'll learn how to manipulate the concepts of
injectivity and surjectivity in Lean.

The notation for functions is the usual one in mathematics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of *all* functions from `X` to `Y` (so `X → Y`
is what mathematicians sometimes call `Hom(X,Y)`), and `f : X → Y`
means that `f` is a term of type `X → Y`, i.e., a function
from `X` to `Y`.

One thing worth mentioning is that the simplest kind of function
evaluation, where you have `x : X` and `f : X → Y`, doesn't need
brackets: you can just write `f x` instead of `f(x)`. You only
need it when evaluating a function at a more complex object;
for example if we also had `g : Y → Z` then we can't write
`g f x` for `g(f(x))`, we have to write `g(f x)` otherwise
`g` would eat `f` and get confused. Without brackets,
a function just eats the next term greedily.

## The API we'll be using

Lean has the predicates `Function.Injective` and `Function.Surjective` on functions.
In other words, if `f : X → Y` is a function, then `Function.Injective f`
and `Function.Surjective f` are true-false statements.

-/

-- Typing `Function.` gets old quite quickly, so let's open the function namespace
open Function
-- using namespace

-- Now we can just write `Injective f` and `Surjective f`.
-- Because of a cunning hack in Lean we can also write `f.Injective` and `f.Surjective`.

-- Our functions will go between these sets, or Types as Lean calls them
variable (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

-- this proof works, because `injective f`
-- means ∀ a b, f a = f b → a = b *by definition*
-- so the proof is "it's reflexivity of `↔`"
-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) : id x = x := by
  rfl

-- Function composition is `∘` in Lean (find out how to type it by putting your cursor on it).
-- The *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.
example : Injective (id : X → X) := by
  intro a b idab
  assumption

-- {n : ℕ | x > 2 ∧ x^n + y^n = z^n} = ∅

example : Surjective (id : X → X) := by
  intro x
  use x
  rfl

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) := by
  intro a b gfab
  specialize hg gfab
  specialize hf hg
  assumption



-- Theorem: composite of two surjective functions
-- is surjective.
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) := by
  intro z
  obtain ⟨ y, hy ⟩ := hg z
  obtain ⟨ x, hx ⟩ := hf y
  use x
  rw [← hy]
  rw [← hx]
  rfl


example (a b c d : ℕ) (h : c = d) : (a + b - b) + c = a + d := by
  rw [h]
  congr
  omega




-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by
  intro ingf
  intro a b fab
  apply ingf
  simp
  rw [fab]



example : ∃ S U T : Type, ∃ f : S → U, ∃ g : U → T, Injective (g ∘ f) ∧  ¬Injective g := by
  use ({ 1 } : Set ℕ)
  use ℕ
  use ℕ
  use (fun (n) => n )
  use (fun (n) => n / 2)
  constructor
  · intro x y
    simp
    intro hxy
    apply Subtype.ext
    rw [x.property]
    rw [y.property]
  · intro inj
    have prop : 4 / 2 = 5 / 2 := by omega
    specialize inj prop
    have prop₂ : 4 ≠ 5 := by omega
    apply prop₂
    assumption






-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by
  intro surj
  intro z
  obtain ⟨ x, hx ⟩ := surj z
  use (f x)
  assumption


end Section3sheet1
