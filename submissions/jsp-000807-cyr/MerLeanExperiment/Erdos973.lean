import MerLeanExperiment.Statement

/-!
# The catalog adapter for Erdős problem 973

The paper proves `UniformExteriorLowerBound`.  This file isolates the final
logical and real-exponential conversion from that stronger theorem to the
literal yes/no target.
-/

open Finset

namespace Erdos973

/-- Luo--Yang--Zhu's uniform lower bound negates the exact affirmative
statement in Erdős problem 973. -/
theorem target_of_uniformExteriorLowerBound
    (h : UniformExteriorLowerBound) : Target := by
  intro hpositive
  rcases hpositive with ⟨C, hC, hconfig⟩
  have hC0 : 0 < C := lt_trans zero_lt_one hC
  have hlog : 0 < Real.log C := Real.log_pos hC
  obtain ⟨N, hN⟩ := h (Real.log C) hlog
  let n : ℕ := max N 2
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn2 : 2 ≤ n := Nat.le_max_right _ _
  obtain ⟨z, hz1, hzext, hzsmall⟩ := hconfig n hn2
  obtain ⟨k, hk, hklarge⟩ := hN n hnN z hzext
  have hksmall := hzsmall k hk
  have hrpow : C ^ (-(n : ℝ)) = Real.exp (-Real.log C * (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hC0]
    congr 1
    ring
  rw [← hrpow] at hklarge
  exact (not_lt_of_ge hklarge.le) hksmall

end Erdos973
