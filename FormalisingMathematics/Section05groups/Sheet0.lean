import Mathlib.Tactic


class DoubMagma (G : Type) extends Mul G : Type where
  mul_xxy : ∀ x y : G, x * (x * y) = y
  mul_yxx : ∀ x y : G, (y * x) * x = y


-- x * y = x * (y * (y * x)) (y * x) = x (y x)
theorem doubMagma_comm (G : Type) [DoubMagma G] : ∀ x y : G, x * y = y * x := by
  intro x y
  calc
    x * y = x * ((y * (y * x)) * (y * x)) := by rw [DoubMagma.mul_yxx (y * x) y]
    _ = x * (x * (y * x)) := by rw [DoubMagma.mul_xxy y x]
    _ = (y * x) := by exact (DoubMagma.mul_xxy x (y * x))
