/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics
set_option linter.all false

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  -- intro h

  -- change (True → False) → False
  intro hnt
  change (True → False) at hnt
  apply hnt
  trivial
  done

example : False → ¬True := by
  intro hf
  exfalso
  assumption
  done

example : ¬False → True := by
  intro hnf
  trivial
  done

example : True → ¬False := by
  intro ht
  change (False → False)
  intro hf
  assumption
  done

example : False → ¬P := by
  intro hf
  exfalso
  assumption
  done

example : P → ¬P → False := by
  intro hp
  intro hnp
  change (P → False) at hnp
  apply hnp
  assumption
  done

example : P → ¬¬P := by
  intro hp
  change (P → False) → False
  intro hnp
  apply hnp
  assumption
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq
  change (P → False)
  intro hP
  change (Q → False) at hnq
  apply hnq
  apply hpq
  assumption
  done

example : ¬¬False → False := by
  intro hnnf
  change ((False → False) → False) at hnnf
  apply hnnf
  intro hf
  assumption
  done

example : ¬¬P → P := by
  intro hnnp
  change (P → False) → False at hnnp
  by_contra hnp
  change (P → False) at hnp
  apply hnnp at hnp
  assumption
  done

example : ¬¬P → P := by
  intro hnnp
  by_cases h : P
  assumption
  change (P → False) → False at hnnp
  change (P → False) at h
  apply hnnp at h
  exfalso
  assumption
  done

example : (¬Q → ¬P) → P → Q := by
  intro hnqp
  intro hp
  by_contra hnq
  apply hnqp at hnq
  apply hnq at hp
  assumption
  done
