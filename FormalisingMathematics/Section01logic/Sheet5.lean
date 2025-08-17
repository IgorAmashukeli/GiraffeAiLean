/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hpq
  rewrite [hpq]
  rfl
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hpq
  rw [hpq]
  intro hqp
  rw [hqp]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  rewrite [hpq]
  assumption
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hpq
  cases' hpq with hp hq
  constructor
  assumption'
  intro hqp
  cases' hqp with hq hp
  constructor
  assumption'
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  intro hpqr
  cases' hpqr with hpq hr
  cases' hpq with hp hq
  constructor
  assumption
  constructor
  assumption'
  intro hpqr
  cases' hpqr with hp hqr
  cases' hqr with hq hr
  constructor
  constructor
  assumption'
  done

example : P ↔ P ∧ True := by
  constructor
  intro hp
  constructor
  assumption
  trivial
  intro hpt
  cases' hpt with hp ht
  assumption
  done

example : False ↔ P ∧ False := by
  constructor
  intro hf
  exfalso
  assumption
  intro hpf
  cases' hpf with hp hf
  assumption
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq
  intro hrs
  constructor
  intro hpr
  cases' hpr with hp hr
  constructor
  rw [← hpq]
  assumption
  rw [← hrs]
  assumption
  intro hqs
  constructor
  cases' hqs with hq hs
  rw [hpq]
  assumption
  cases' hqs with hq hs
  rw [hrs]
  assumption
  done

example : ¬(P ↔ ¬P) := by
  intro hpnp
  have hnp : ¬P := by
    cases' hpnp with hpn hnpp
    intro hp
    apply hpn <;> assumption
  apply hnp
  rw [hpnp] <;> assumption
  done
