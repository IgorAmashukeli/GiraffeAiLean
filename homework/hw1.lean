import Mathlib.Tactic
/-!
# Инструкция по выполнению ДЗ №1.
Вам предлагается заменить `sorry` на валидные доказательства в примерах ниже.
Используйте только тактики, пройденные на первой лекции, а именно:
* `intro`
* `exact`
* `apply`
* `cases'`
* `constructor`
* `left`/`right`
* `change`
* `exfalso`
* `by_cases`
* `trivial`
* `rfl`
* `rw`

Не стесняйтесь спрашивать вопросы в чате!
-/

/-- Problem 1. -/
example : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq hp
  apply hnq
  apply hpq
  exact hp

/-- Problem 2. -/
example : (P ↔ True) → (Q ↔ False) → (P ∧ ¬Q ↔ True) := by
  intro hpt hqf
  constructor
  intro hpq
  trivial
  intro ht
  constructor
  rw [hpt]
  trivial
  intro hq
  rw [← hqf]
  exact hq


/-- Problem 3. -/
example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro hpq
    by_cases hp : P
    · by_cases hq : Q
      · exfalso
        apply hpq
        constructor
        · exact hp
        · exact hq
      · right
        exact hq
    · left
      exact hp
  · intro hnpq
    intro hpq
    cases' hpq with hp hq
    cases' hnpq with hnp hnq
    apply hnp
    exact hp
    apply hnq
    exact hq
