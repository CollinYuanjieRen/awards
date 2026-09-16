import MerLeanExperiment.CountBridge
import MerLeanExperiment.IntervalRegularity
import MerLeanExperiment.RotationOrbit

/-! Exact equality between the original visit discrepancy and circle Birkhoff sums. -/

namespace Kesten

open AddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The centered visit count is the Birkhoff sum of the centered circle interval indicator. -/
theorem birkhoffSum_eq_count_discrepancy (α u v : ℝ) (n : ℕ) :
    birkhoffSum (fun x : AddCircle (1 : ℝ) ↦ x + (α : AddCircle (1 : ℝ)))
        (fun x ↦ intervalIndicator u v x - (v - u)) n (α : AddCircle (1 : ℝ)) =
      (countInIco α u v n : ℝ) - (n : ℝ) * (v - u) := by
  rw [count_discrepancy_eq_sum]
  unfold birkhoffSum
  apply Finset.sum_congr rfl
  intro j _
  rw [rotation_iterate_apply]
  have horbit : (α : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ)) =
      ((α * (j + 1 : ℕ) : ℝ) : AddCircle (1 : ℝ)) := by
    calc
      (α : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ)) =
          ((α + j * α : ℝ) : AddCircle (1 : ℝ)) := by norm_num [nsmul_eq_mul]
      _ = ((α * (j + 1 : ℕ) : ℝ) : AddCircle (1 : ℝ)) := by
        congr 1
        push_cast
        ring
  rw [horbit]
  change intervalIndicator u v ((α * (j + 1 : ℕ) : ℝ) : AddCircle (1 : ℝ)) -
      (v - u) = _
  rw [intervalIndicator_coe]

end Kesten
