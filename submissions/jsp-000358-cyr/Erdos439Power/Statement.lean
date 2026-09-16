import Mathlib

/-!
The positive-integer form of Erdős 439, including every fixed exponent at least two.
Only the two summands are required to have the same colour. They are positive
and distinct; the power itself has its ordinary natural-number meaning.
-/

namespace Erdos439Power

/-- Every finite colouring has two distinct positive summands of a `k`th power. -/
def PowerSumStatement (k : ℕ) : Prop :=
  ∀ r : ℕ, ∀ colour : ℕ → Fin r,
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧
      colour x = colour y ∧ x + y = z ^ k

/-- Both the square question and the question for every higher fixed power. -/
def FullStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → PowerSumStatement k

/-- The corresponding original integer-domain formulation. -/
def IntegerStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ colour : ℤ → Fin r,
    ∃ x y z : ℤ, x ≠ y ∧ colour x = colour y ∧ x + y = z ^ k

end Erdos439Power
