/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hp
  left
  assumption
  done

example : Q → P ∨ Q := by
  intro hq
  right
  assumption
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq
  intro hpr
  intro hqr
  cases' hpq with hp hq
  apply hpr
  assumption
  apply hqr
  assumption
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hpq
  cases' hpq with hp hq
  right
  assumption
  left
  assumption
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  intro hpqr
  cases' hpqr with hpq hr
  cases' hpq with hp hq
  left <;> assumption
  right <;> left <;> assumption
  right <;> right <;> assumption
  intro hpqr
  cases' hpqr with hp hqr
  left <;> left <;> assumption
  cases' hqr with hq hr
  left <;> right <;> assumption
  right <;> assumption
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hpr hqs hpq
  cases' hpq with hp hq
  left <;> apply hpr <;> assumption
  right <;> apply hqs <;> assumption
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hpq hpr
  cases' hpr with hp hr
  left <;> apply hpq <;> assumption
  right <;> assumption
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hpr hqs
  rw [hpr]
  rw [hqs]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro hpq <;> constructor <;> intro hp <;> apply hpq
  left <;> assumption
  right <;> assumption
  intro hnpq <;> intro hpq <;> cases' hnpq with hnp hnq <;> cases' hpq with hp hq
  apply hnp <;> assumption
  apply hnq <;> assumption
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro hnp <;> by_cases hp : P
  by_cases hq : Q
  exfalso <;> apply hnp <;> constructor <;> assumption
  right <;> assumption
  left <;> assumption
  intro hnpq <;> intro hpq <;> cases' hnpq with hnp hnq <;> cases' hpq with hp hq
  apply hnp <;> assumption
  apply hnq <;> assumption
  done
