import MerLeanExperiment.ClusterUpper
import MerLeanExperiment.ThreeCenterData

/-!
The unconditional upper construction for Sendov's first large-cardinality interval.
-/

namespace PlanarMinimax

/-- The explicit three-center binary clusters give the first sharp upper formula. -/
theorem minimaxAngle_le_threeCenter {m N : ℕ} (hm : 2 ≤ m) (hN : 3 ≤ N)
    (hcard : N ≤ 2 ^ m + 2 ^ (m - 2)) :
    minimaxAngle N ≤ Real.pi * (1 - 2 / (2 * (m : ℝ) + 1)) := by
  have hcount : N ≤ ∑ t : Fin 3, 2 ^ threeDepth m t := by
    rw [threeDepth_cardinality hm]
    exact hcard
  have hbound : minimaxAngle N ≤ Real.pi - threeDelta m := by
    apply minimaxAngle_le_cluster hN hcount (threeCenter m) (threeCenter_injective hm)
      (threeInternalVector m) (threeInternalVector_ne_zero m)
      (sub_nonneg.mpr (threeDelta_le_pi hm))
    · intro t r s hrs σ τ
      change InnerProductGeometry.angle (threeSignedInternal σ m t r)
        (threeSignedInternal τ m t s) ≤ Real.pi - threeDelta m
      exact threeInternal_within_le hm t hrs σ τ
    · intro t r s hts σ
      change InnerProductGeometry.angle (threeSignedInternal σ m t r)
        (threeCenter m s - threeCenter m t) ≤ Real.pi - threeDelta m
      exact threeInternal_external_le hm t s hts r σ
    · intro i j l hij hjl hil
      simpa [EuclideanGeometry.angle, vsub_eq_sub] using
        threeCenter_triples_le hm i j l hij hjl hil
  rw [threeCap_formula] at hbound
  exact hbound

#print axioms minimaxAngle_le_threeCenter

end PlanarMinimax
