import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics.Section02reals.Sheet5 -- import a bunch of previous stuff
open Section2sheet3 -- чтобы иметь определение `TendsTo`
open Section2sheet5
/-!
# Инструкция по выполнению ДЗ №2.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
На полный балл достаточно решить **любые 2 задачи**.
Могут оказаться полезными следующие тактики:
* `use` для подстановки значения в квантор `∃` в цели
* `obtain` для "распаковки" квантора `∃` в гипотезах
* `specialize` для подстановки значения в квантор `∀` в гипотезе

* `norm_num` для упрощения выражений содержащих нумералы
* `ring_nf`/`ring` для упрощения выражений в кольцах (и `ℝ` в частности)
* `linarith` для решения линейных уравнений/неравенств
* `simp` для упрощения выражений и раскрытия определений

* `exact?` для поиска в библиотеке подходящей леммы, которая бы закрыла цель при помощи `exact`.
* `rw?` для поиска леммы, которая бы упростила или закрыла цель при помощи тактики `rw`.

* `have` для введения вспомогательных гипотез в контекст

Пользуйтесь так же теоремами доказанными на лекции (они должны быть доступны благодаря `import` и `open` выше).

Не стесняйтесь спрашивать вопросы в чате!
-/


/-- Задача 1.
Комментарий: на самом деле условие `hc` не требуется. Можете попробовать его убрать доказать факт в общем случае.
-/
lemma tendsTo_pos_const_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) (c : ℝ) (hc : 0 < c) :
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


lemma tendsTo_neg_const_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) (c : ℝ) (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have minclz : - c > 0 := by linarith
  have negtend := tendsTo_pos_const_mul a t h (-c) (minclz)
  have postend := tendsTo_neg negtend
  simp at postend
  assumption


example (a : ℕ → ℝ) (t : ℝ) (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  have hcz : (c > 0 ∨ c ≤ 0) := by exact lt_or_le 0 c
  cases' hcz with hc hc
  exact tendsTo_pos_const_mul a t h c hc
  have hcz : (c = 0 ∨ c < 0) := by exact Decidable.eq_or_lt_of_le hc
  cases' hcz with hc2 hc2
  · rw [hc2]
    simp
    apply tendsTo_const
  · exact tendsTo_neg_const_mul a t h c hc2

/-- Задача 2.
`x ∣ y` означает "`x` делит `y`". Тактика `norm_num` умеет доказывать делимость для числовых выражений.
Подсказка: сократить доказательство поможет комбинатор `<;>`.
-/



example : ∀ (a b c : ℤ), ∃ m, (a = 1 ∨ a = 9) → (b = 3 ∨ b = 5) → (c = 42 ∨ c = 24) → m ∣ (a + b + c) := by
  intro a b c
  use 1
  rintro (ha | ha) (hb | hb) (hc | hc)
  all_goals
    rw [ha, hb, hc]
    norm_num





/-- Задача 3 (сложная). -/
example (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
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
