/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the tactics

/-!

# Challenge sheet

This is a harder group theory question.

It turns out that two of the axioms in the standard definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group, by
proving the other axioms?

-/

namespace Section5sheet2


-- removing `mul_one` and `mul_inv_self` from the five standard axioms
-- for a group.
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup

-- Let `G` be a "weak group" and say a,b,c are in G
variable {G : Type} [WeakGroup G] (a b c : G)

/-

The (tricky) challenge is to prove that G is a group, which we can interpret as
proving the missing axioms `mul_one` and `mul_inv_self`. Note that you
can't use the `group` tactic any more because `G` isn't a group yet:
this is what you're trying to prove!

One way of doing it: try proving

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  calc
    b = 1 * b := (one_mul b).symm
    _ = a⁻¹ * a * b := by rw [inv_mul_self a]
    _ = a⁻¹ * (a * b) := mul_assoc a⁻¹ a b
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = a⁻¹ * a * c := (mul_assoc a⁻¹ a c).symm
    _ = 1 * c := by rw [inv_mul_self a]
    _ = _ := one_mul c


theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  apply mul_left_cancel a⁻¹ (a * b) c
  calc
    _ = a⁻¹ * a * b := (mul_assoc a⁻¹ a b).symm
    _ = 1 * b := by rw [inv_mul_self a]
    _ = b := by rw [one_mul b]
    _ = _ := h


theorem mul_one (a : G) : a * 1 = a := by
  apply mul_eq_of_eq_inv_mul
  exact (inv_mul_self a).symm


theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one a⁻¹]


end WeakGroup




/-

If you want to take this further: prove that if we make
a new class `BadGroup` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `mul_inv_self`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first.

-/
-- claim: not a group in general
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

-- `Bool` is a type with two terms, `Bool.true` and `Bool.false`. See if you can make it into
-- a bad group which isn't a group!
instance : One Bool := {one := Bool.true}

instance : Mul Bool :=
  {mul := fun (el : Bool) => fun (_ : Bool) => el}

instance : Inv Bool :=
  {inv := fun (_ : Bool) => Bool.true}

instance : BadGroup Bool where
  mul_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  -- `decide`, might be able to do this
  mul_one := by intro a; cases a <;> rfl
  -- decide
  inv_mul_self := by intro a ; cases a <;> rfl
  -- decide

example : ¬∀ a : Bool, 1 * a = a := by
  intro h
  specialize h Bool.false
  have prop₀ : 1 * false = 1 := by rfl
  rw [prop₀] at h
  cases h
