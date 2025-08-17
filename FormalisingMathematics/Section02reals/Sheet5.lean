/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import FormalisingMathematics.Section02reals.Sheet3
-- import the definition of `TendsTo` from a previous sheet

namespace Section2sheet5

open Section2sheet3

-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) :
TendsTo (fun n ↦ -a n) (-t) := by
  simp [TendsTo] at ha ⊢
  intro ε hε
  specialize ha ε hε
  cases' ha with N hN
  use N
  intro n hn
  specialize hN n hn
  rw [← abs_neg (- a n + t)]
  ring_nf
  assumption

/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) := by
  simp [TendsTo] at ha hb ⊢
  intro ε hε
  have hε2 : 0 < ε / 2  := by
    exact half_pos hε
  specialize ha (ε / 2) hε2
  specialize hb (ε / 2) hε2
  cases' ha with B₀ hB₀
  cases' hb with B₁ hB₁
  use (max B₀ B₁)
  intro n hn
  have B₀ln : B₀ ≤ n := by
    exact le_of_max_le_left hn
  have B₁ln : B₁ ≤ n := by
    exact le_of_max_le_right hn
  specialize hB₀ n B₀ln
  specialize hB₁ n B₁ln
  have eq1 : a n + b n - (t + u) = (a n - t) + (b n - u) := by linarith
  calc
    |a n + b n - (t + u)| = |(a n - t) + (b n - u)| := by rw [eq1]
    |(a n - t) + (b n - u)| ≤ |a n - t| + |b n - u| := by exact abs_add_le (a n - t) (b n - u)
    |a n - t| + |b n - u| < ε := by linarith




/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.

  apply tendsTo_add
  assumption
  apply tendsTo_neg
  assumption

end Section2sheet5
