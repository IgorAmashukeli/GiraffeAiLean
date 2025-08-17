import Mathlib.Tactic

inductive Weekday
| monday : Weekday
| tuesday : Weekday
| sunday : Weekday

example : Weekday.monday ≠ .sunday := by
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

inductive Foo
| mk1 (n : Nat)
| mk2

#check Foo.mk1 3
#check Foo.mk2

inductive Prod' (α β : Type)
| makePair (a : α) (b : β)

#check Prod'

#check Prod'.makePair (1 : Nat) (-2 : Int)

inductive Sum' (α β : Type)
| left (a : α)
| right (b : β)

#check (Sum'.left 1 : Sum' Nat Int)
#check (Sum'.right (-1) : Sum' Nat Int)

#check And

inductive And' (P Q : Prop)
| mk (p : P) (q : Q)

inductive Or' (P Q : Prop)
| left (p : P)
| right (q : Q)

def parse (val : String) : (α : Type) × α := sorry

#check (α : Type) × α

-- To be continued...


mutual
  inductive Even'
  | zero
  | succ (x : Odd')

  inductive Odd'
  | succ (x : Even')
end

example (P Q : Prop) : And' P Q → Or' P Q := by
  intro hand
  cases' hand with hp hq
  exact Or'.left hp

theorem foo (P Q : Prop) : Or' P Q → P ∨ Q := by
  intro h
  cases' h with hp hq
  left
  assumption
  right
  assumption


example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor <;> assumption

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := And.intro hP hQ

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨ ?_, ?_⟩
  · exact hP
  · exact hQ


example (a b : ℕ) (h : a < b) : a < b + 2 := by
  omega

example (a b : ℕ) (h : a = b) (h2 : a + 1 ≤ a * 2) : b + 1 ≤ b * 2 := by
  convert h2 <;> exact h.symm


def sum (n : Nat) : Nat := match n with
| Nat.zero => Nat.zero
| Nat.succ m => sum m + n -- n = m + 1



example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n with m ih
  · simp ; rfl
  · unfold sum
    have prop₀ : 2 * (sum m + (m + 1)) = 2 * sum m + 2 * (m + 1) := by omega
    rw [prop₀]
    rw [ih]
    have prop₁ : (m + 1 + 1) = (m + 2) := by omega
    rw [prop₁]
    ring


theorem sum_th (n : ℕ) : 2 * sum n = n * (n + 1) := by
  cases' n with m
  · simp ; rfl
  · unfold sum
    ring_nf
    rw [mul_comm, sum_th m]
    ring_nf


example (n : ℕ) : 2 * sum n = n * (n + 1) := by
  induction' n using Nat.strong_induction_on with n ih
  cases n with
  | zero => simp ; unfold sum ; rfl
  | succ m =>
    specialize ih m (by omega)
    unfold sum
    ring_nf
    rw [mul_comm, ih]
    ring_nf


#check Unit
