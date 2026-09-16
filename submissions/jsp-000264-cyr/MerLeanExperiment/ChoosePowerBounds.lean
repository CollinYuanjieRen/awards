import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace ReciprocalSquares

/-- A simple factorial-weighted lower bound for a binomial coefficient. -/
theorem pow_le_factorial_mul_choose (R K r : ℕ) (hr : r ≤ R + 1) (hK : 2 * R ≤ K) :
    R ^ r ≤ r.factorial * K.choose r := by
  have hsub : R ≤ K + 1 - r := by omega
  calc
    R ^ r ≤ (K + 1 - r) ^ r := Nat.pow_le_pow_left hsub r
    _ ≤ K.descFactorial r := Nat.pow_sub_le_descFactorial K r
    _ = r.factorial * K.choose r := Nat.descFactorial_eq_factorial_mul_choose K r

end ReciprocalSquares
