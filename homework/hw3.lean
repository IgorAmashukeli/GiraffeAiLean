import Mathlib
/-!
# Инструкция по выполнению ДЗ №3.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
На полный балл достаточно решить **любые 2 задачи**.

Могут оказаться полезными:
* Тактика `ext` для для применения правил экстенсиональности (для множеств, функций, ...)
* Тактика `unfold` для распаковки определений
* Если цель имеет вид `A ⊆ B` можно сразу использовать `intro x hx` где `hx : x ∈ A` и переходить к цели `x ∈ B`
* Точно так же если есть гипотеза `h : A ⊆ B` то можно использовать ее для `apply`: к примеру если `h_mem : x ∈ A`
  то `apply h at h_mem` заменит ее на `h_mem : x ∈ B`.
* Если Вам нужен некоторый вспомогательный факт `Some_New_Fact` и вы чувствуете что он
  должен выводиться из текущего контекста при помощи лемм из библиотеки можно использовать
  синтаксис `have h_new : Some_New_Fact := by exact?`
* `rw [← h]` для переписывания цели/гипотезы при помощи `h` используя `h` в обратном направлении (справа налево)
* `simp` для упрощения выражений.

## Небольшая справка о `simp`
`simp` работает как `rw`, но кроме переданных ему лемм (которых вообще может не быть) он использует леммы
вида `A = B` или `A ↔ B` из библиотеки помеченные аттрибутом `@[simp]`. Если какое-то подвыражение текущей цели
совпадает с левой частью в лемме, то она заменяется на правую часть. Цель тактики `simp` -- привести
выражение к "нормальной форме" насколько это возможно. Например есть `simp`-леммы
в которых доказано `|1| = 1`, `p ∧ True ↔ p`, `List.length List.nil = 0`, `x ∈ {y | P y} ↔ P x` и т.п.
Применяя `simp` к выражениям содержащим левые части этих лемм, мы упрощаем эти выражения и с ними становится
легче работать.

Подробнее можно прочитать в секциях Rewriting и Using the Simplifier здесь:
https://leanprover.github.io/theorem_proving_in_lean4/tactics.html

Не стесняйтесь задавать вопросы в чате!
-/

/-- Задача 1.

Комментарий: эта задача решается в одну строчку тактикой `tauto_set`.
Вам нужно справиться без нее, хотя тактика `tauto` не заперещена.
-/
example {X : Type} (A B C : Set X) (h : A ∪ B ⊆ C) : Cᶜ ⊆ Aᶜ ∩ Bᶜ := by
  intro x hx
  constructor
  intro xa
  have prop : x ∈ C := by apply h ; left ; assumption
  apply hx
  assumption
  intro xb
  have prop : x ∈ C := by apply h; right ; assumption
  apply hx
  assumption

/-- Задача 2. -/
example : ∃ f : ℕ → ℕ × ℕ, f '' {n | Even n} = {(n, m) | n = m} := by
  use (fun (n : ℕ) => (n / 2, (n + 1) / 2) : ℕ → ℕ × ℕ)
  ext pr
  constructor
  · intro hpr
    simp at hpr ⊢
    obtain ⟨N, hN⟩ := hpr
    obtain ⟨ he, hN ⟩ := hN
    rw [← hN]
    simp
    simp [Even] at he
    obtain ⟨ r, hr ⟩ := he
    rw [hr]
    omega
  · intro hpr
    simp at hpr ⊢
    use (pr.1 + pr.1)
    constructor
    simp
    have prop₁ : (pr.1 + pr.1) / 2 = pr.1 := by omega
    rw [prop₁]
    have prop₂ : (pr.1 + pr.1 + 1) / 2 = pr.2 := by omega
    rw [prop₂]


def IsLinear (f : ℚ → ℚ) : Prop := ∃ c, ∀ x, f x = c * x

/-- Задача 3. -/
example : {f : ℚ → ℚ | IsLinear f ∧ ∀ x, |f x| = |x|} = {id, -id} := by
  ext f
  constructor
  · intro hf
    simp at hf ⊢
    cases' hf with hlin habs
    obtain ⟨ c, hc ⟩ := hlin
    specialize habs 1
    have hc1 := hc 1
    simp at hc1
    rw [hc1] at habs
    simp at habs
    have prop₁ : c = 1 ∨ c = -1 := by exact abs_eq_abs.mp habs
    cases' prop₁ with hco hcmo
    left
    funext x
    specialize hc x
    rw [hco] at hc
    simp at hc ⊢
    assumption
    right
    funext x
    specialize hc x
    rw [hcmo] at hc
    simp at hc ⊢
    assumption
  · intro hf
    simp at hf ⊢
    cases' hf with hfid hfid <;> rw [hfid] <;> simp
    use 1 ;  intro x ; simp
    use (-1) ; intro x ; simp
