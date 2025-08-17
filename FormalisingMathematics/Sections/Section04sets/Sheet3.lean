/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro hx₁ hx₂
  apply hx₁
  assumption

example : x ∈ A → x ∉ A → False := by
  intro hx hx₂
  apply hx₂
  assumption

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB xnB xnA
  apply xnB
  apply hAB
  assumption

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro hx
  assumption

example : x ∈ Aᶜ → x ∉ A := by
  intro hx
  assumption

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hx
    intro hx₂
    obtain ⟨ N, hN ⟩ := hx₂
    specialize hx N
    apply hN
    assumption
  · intro hA
    intro x
    by_contra hx
    apply hA
    use x
    assumption




example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · intro hA
    intro hAc
    obtain ⟨ N, hN ⟩ := hA
    specialize hAc N
    apply hAc
    assumption
  · intro hAc
    by_contra hnex
    apply hAc
    intro x
    intro hx
    apply hnex
    use x
