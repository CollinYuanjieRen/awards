import MerLeanExperiment.Necessity
import MerLeanExperiment.Sufficiency

/-! Full Hecke–Ostrowski–Kesten characterization of interval bounded remainder. -/

namespace Kesten

/-- An interval has bounded discrepancy under an irrational rotation exactly when its length
belongs to `ℤ α + ℤ`. -/
theorem bounded_remainder_iff (α u v : ℝ) (hα : Irrational α) (hu : 0 ≤ u)
    (huv : u < v) (hv : v ≤ 1) : Kesten.HasBoundedRemainder α u v ↔
    ∃ k l : ℤ, v - u = (k : ℝ) * α + (l : ℝ) := by
  constructor
  · exact integer_relation_of_bounded_remainder α u v hα huv
  · exact bounded_remainder_of_integer_relation α u v hu huv hv

end Kesten
