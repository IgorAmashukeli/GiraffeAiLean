/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  · intro hx
    cases' hx with hx hx <;> assumption
  · intro hx
    left
    assumption

example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := by
  ext n
  apply h
-- #check propext

example : A ∩ A = A := by
  ext x
  constructor
  · intro hx
    cases' hx with hx hx
    assumption
  · intro hx
    constructor <;> assumption


example : A ∩ ∅ = ∅ := by
  ext n
  constructor
  · intro hx
    cases' hx with hx hx
    assumption
  · intro hx
    constructor <;> exfalso <;> assumption

example : A ∪ univ = univ := by
  ext x
  constructor
  · intro hx
    cases' hx with hx hx <;> trivial
  . intro hx
    right
    trivial

example : A ⊆ B → B ⊆ A → A = B := by
  intro hab hba
  ext x
  constructor
  · intro hx
    apply hab
    assumption
  · intro hx
    apply hba
    assumption


example : A ∩ B = B ∩ A := by
  ext x
  constructor <;> intro hx <;> cases' hx with hxA hxB <;> constructor <;> assumption

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  · intro hx
    cases' hx with hxa hxbc
    cases' hxbc with hxb hxc
    constructor; constructor
    assumption'
  · intro hx
    cases' hx with hxab hxc
    cases' hxab with hxa hxb
    constructor
    assumption
    constructor
    assumption'

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · intro hx
    cases' hx with hxA hxbc
    left ; left ; assumption
    cases' hxbc with hxB hxC
    left ; right ; assumption
    right ; assumption
  · intro hx
    cases' hx with hxAB hxC
    cases' hxAB with hxA hxB
    left ; assumption
    right ; left ; assumption
    right ; right ; assumption

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro hx
    constructor
    cases' hx with hxA hxBC
    left ; assumption
    right ; cases' hxBC with hxB hxC ; assumption
    cases' hx with hxA hxBC
    left ; assumption
    cases' hxBC with hxB hxC
    right
    assumption
  · intro hx
    cases' hx with hxAB hxAC
    cases' hxAB with hxA hxB
    left ; assumption
    cases' hxAC with hxA hxC
    left ; assumption
    right; constructor <;> assumption


example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  · intro hx
    cases' hx with hxA hxBC
    cases' hxBC with hxB hxC
    left ; constructor <;> assumption
    right ; constructor <;> assumption
  · intro hx
    cases' hx with hxAB hxAC
    cases' hxAB with hxA hxB
    constructor ; assumption ; left ; assumption
    cases' hxAC with hxA hxC
    constructor ; assumption ; right ; assumption
