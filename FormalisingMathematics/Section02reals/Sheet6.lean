/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3 Section2sheet5

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  simp [TendsTo] at *
  intro ε hε
  obtain ⟨ N, hN ⟩ := h (ε / 37) (by linarith)
  use N
  intro n hn
  specialize hN n hn
  rw [abs_lt] at *
  have lh := hN.1
  have rh := hN.2
  constructor <;> linarith



/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  simp [TendsTo] at *
  intro ε hε
  obtain ⟨ N, hN ⟩ := h (ε / c) (div_pos hε hc)
  clear h
  use N
  intro n hn
  specialize hN n hn
  have eqmod : |c| = c := by exact abs_of_pos hc
  calc
    |c * a n - c * t| = |c * (a n - t)| := by ring_nf
    _ = |c| * |a n - t| := by exact abs_mul c (a n - t)
    _ = c * |a n - t| := by rw [eqmod]
    _ < c * (ε / c) := by exact (mul_lt_mul_left hc).mpr hN
     c * (ε / c) = (ε / c) * c := by linarith
     (ε / c) * c = ε := by exact div_mul_cancel₀ ε (by linarith)





/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have minclz : - c > 0 := by linarith
  have negtend := tendsTo_pos_const_mul h (minclz)
  have postend := tendsTo_neg negtend
  simp at postend
  assumption

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have hcz : (c > 0 ∨ c ≤ 0) := by exact lt_or_le 0 c
  cases' hcz with hc hc
  exact tendsTo_pos_const_mul h hc
  have hcz : (c = 0 ∨ c < 0) := by exact Decidable.eq_or_lt_of_le hc
  cases' hcz with hc2 hc2
  · rw [hc2]
    simp
    apply tendsTo_const
  · exact tendsTo_neg_const_mul h hc2




/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  have prop₁ := tendsTo_const_mul c h
  have eq₁ : (fun n ↦ a n * c) = (fun n ↦ c * a n) := by
    funext n
    exact CommMonoid.mul_comm (a n) c
  have eq₂ := CommMonoid.mul_comm t c
  rw [eq₁]
  rw [eq₂]
  assumption


-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by

  have prop₁ := tendsTo_add h1 h2
  simp at prop₁
  exact prop₁

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  · intro h
    have prop₁ := tendsTo_sub h (tendsTo_const t)
    simp at prop₁
    assumption
  · intro h
    have prop₁ := tendsTo_of_tendsTo_sub h (tendsTo_const t)
    simp at prop₁
    assumption

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
    simp [TendsTo] at *
    intro ε hε
    obtain ⟨ N, hN ⟩ := ha (√ ε) (by exact Real.sqrt_pos_of_pos hε)
    obtain ⟨ M, hM ⟩  := hb (√ ε) (by exact Real.sqrt_pos_of_pos hε)
    use max M N
    intro n hn
    specialize hM n (by exact le_of_max_le_left hn)
    specialize hN n (by exact le_of_max_le_right hn)
    calc
      |a n * b n| = |a n| * |b n| := by exact abs_mul (a n) (b n)
      _ < (√ ε) * (√ ε) := by exact Right.mul_lt_mul_of_nonneg hN hM (
        by exact abs_nonneg (a n)) (by exact abs_nonneg (b n))
      _ = ε := by refine Real.mul_self_sqrt (by linarith)



/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  have prop₁ := tendsTo_sub_lim_iff.mp ha
  have prop₂ := tendsTo_sub_lim_iff.mp hb
  have prop₃ : (fun n ↦ a n * b n) =
  (fun n ↦ (a n - t) * (b n - u) + (a n - t) * u + (b n - u) * t + u * t) := by
    funext n
    ring
  rw [prop₃]
  have prop₄ := tendsTo_zero_mul_tendsTo_zero prop₁ prop₂
  have prop₅ := tendsTo_mul_const u prop₁
  have prop₆ := tendsTo_mul_const t prop₂
  simp at prop₅
  simp at prop₆
  have prop₇ := tendsTo_const (u * t)
  have prop₀ : u * t = t * u := by exact CommMonoid.mul_comm u t
  have prop₇₀ : TendsTo (fun x ↦ u * t) (t * u) := Eq.subst (prop₀) (prop₇)
  have prop₈ := tendsTo_add prop₄ prop₅
  have prop₉ := tendsTo_add prop₈ prop₆
  have prop₁₀ := tendsTo_add prop₉ prop₇₀
  simp at prop₁₀
  assumption







-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra sneqt
  have hpos := abs_sub_pos.mpr sneqt
  have hpos2 : |s - t| / 3 > 0 := by linarith
  obtain ⟨ N, hN ⟩ := hs (|s - t| / 3) hpos2
  obtain ⟨ M, hM ⟩ := ht (|s - t| / 3) hpos2
  specialize hN (max M N) (by exact Nat.le_max_right M N)
  specialize hM (max M N) (by exact Nat.le_max_left M N)
  have prop : |s - a (max M N)| = |a (max M N) - s| := by exact abs_sub_comm s (a (M ⊔ N))

  have prop₀ : |s - t| < 2 * |s - t| / 3 := by
    calc
      |s - t| = |(s - a (max M N)) + (a (max M N) - t)| := by ring_nf
      _ <= |s -  a (max M N)| + |a (max M N) - t| := by exact abs_add_le (s - a (max M N)) (a (max M N) - t)
      _ = |a (max M N) - s| + |a (max M N) - t| := by rw [prop]
      _ < (|s - t| / 3) + (|s - t| / 3) := by exact add_lt_add hN hM
      _ = _ := by linarith
  linarith









end Section2sheet6
