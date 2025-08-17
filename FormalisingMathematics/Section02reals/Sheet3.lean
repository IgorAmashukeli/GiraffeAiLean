/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

namespace Section2sheet3

/-

# Limits of sequences in Lean

We give the standard `ε`, `N` definition of the limit of a sequence
and prove some theorems about them.

## `fun` notation for functions

Here's how we define the functions from the naturals to the naturals
sending n to n^2 + 3:

-/

-- def c : ℝ := 2

-- def f : ℕ → ℝ := fun (n : ℕ) ↦ n ^ 2 + 3

-- def g (n : ℕ) := f n

/-

Mathematicians might write `n ↦ n^2+3` for this function. You can
read more about function types in the "three kinds of types" section
of Part B of the course book.

Sometimes you might find yourself with a lambda-defined function
evaluated at a number. For example, you might see something like
`(fun n => n^2 + 3) 37`, which means "take the function sending
`n` to `n^2+3` and then evaluate it at 37". You can use the `dsimp`
(or `dsimp only`) tactic to simplify this to `37^2+3`.

The reason we need to know about function notation for this sheet
is that a sequence `x₀, x₁, x₂, …` of reals on this sheet will
be encoded as a function from `ℕ` to `ℝ` sending `0` to `x₀`, `1` to `x₁`
and so on.

## Limit of a sequence.

Here's the definition of the limit of a sequence.
-/
/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ B : ℕ, ∀ n ≥ B, |a n - t| < ε
/-

We've made a definition, so it's our job to now make the API
for the definition, i.e. prove some basic theorems about it.

-/
-- If your goal is `TendsTo a t` and you want to replace it with
-- `∀ ε > 0, ∃ B, …` then you can do this with `rw tendsTo_def`.
theorem tendsTo_def (a : ℕ → ℝ) (t : ℝ) :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl


example : TendsTo (fun _ ↦ 1) 1 := by
  unfold TendsTo
  intro ε hε
  use (0 : ℕ)
  intro n
  intro hn
  dsimp
  norm_num
  change (0 < ε) at hε
  exact hε


-- the eagle-eyed viewers amongst you might have spotted
-- that `∀ ε > 0, ...` and `∀ ε, ε > 0 → ...` and `∀ ε, 0 < ε → ...`
-- are all definitionally equal, so `rfl` sees through them.
/-

## The questions

Here are some basic results about limits of sequences.
See if you can fill in the `sorry`s with Lean proofs.
Note that `norm_num` can work with `|x|` if `x` is a numeral like 37,
but it can't do anything with it if it's a variable.
-/




/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun _ ↦ c) c := by
  rw [TendsTo]
  intro ε hε
  use (0 : ℕ)
  intro n hn
  norm_num
  assumption


/-- The limit of the constant sequence with value 37 is 37. -/
theorem tendsTo_thirtyseven : TendsTo (fun _ ↦ 37) 37 := by
  apply tendsTo_const


/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
example {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n + c) (t + c) := by
  intro ε hε
  specialize h ε hε
  cases' h with N hN
  use N
  intro n hn
  specialize hN n hn
  ring_nf
  exact hN



-- using simp will automatically simplify:
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n + c) (t + c) := by
  simp [TendsTo] at h ⊢
  assumption



-- you're not quite ready for this one yet though.
/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  simp [TendsTo] at h ⊢
  intro ε hε
  specialize h ε hε
  cases' h with N hN
  use N
  intro n hn
  specialize hN n hn
  have eqmod : |a n - t| = |- a n + t| := by
    have my_h := abs_neg (a n - t)
    rw [← my_h]
    ring_nf
  rw [← eqmod]
  assumption


end Section2sheet3
