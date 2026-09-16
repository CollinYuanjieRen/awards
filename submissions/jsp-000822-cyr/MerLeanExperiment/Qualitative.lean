import MerLeanExperiment.Target
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.MetricSpace.Bounded

namespace DiskDiscrepancy

/-- Finiteness of every disk intersection gives the compact-set counting condition. -/
theorem admissible_of_infinite_of_uniformDiskBound {A : Set Plane} {B : ℝ}
    (hA : A.Infinite) (hB : UniformDiskBound A B) : Admissible A := by
  refine ⟨hA, fun center radius ↦ ?_⟩
  by_cases hr : 0 ≤ radius
  · exact (hB center radius hr).1
  · have he : diskPoints A center radius = ∅ := by
      ext p
      simp only [diskPoints, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hp
      exact hr (dist_nonneg.trans hp)
    rw [he]
    exact Set.finite_empty

/-- A finite point set cannot compensate for the quadratic growth of disk area. -/
theorem not_uniformDiskBound_of_finite {A : Set Plane} (hA : A.Finite) (B : ℝ) :
    ¬ UniformDiskBound A B := by
  intro hB
  let r : ℝ := (A.ncard : ℝ) + |B| + 1
  have hn : (0 : ℝ) ≤ A.ncard := Nat.cast_nonneg _
  have hr : 1 ≤ r := by dsimp [r]; linarith [abs_nonneg B]
  have hcNat : pointCount A 0 r ≤ A.ncard :=
    Set.ncard_le_ncard (fun _ hp ↦ hp.1) hA
  have hc : (pointCount A 0 r : ℝ) ≤ A.ncard := by exact_mod_cast hcNat
  have herr := (hB 0 r (by linarith)).2
  change |(pointCount A 0 r : ℝ) - Real.pi * r ^ 2| ≤ B at herr
  have harea := (abs_le.mp herr).1
  have hrsq : r ≤ r ^ 2 := by nlinarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hproduct := mul_le_mul_of_nonneg_right hpi (sq_nonneg r)
  dsimp [r] at hrsq harea hproduct
  nlinarith [le_abs_self B]

/-- The quantitative lower face implies unboundedness for every finite-count set.

This is a supporting implication. Its lower-bound premise must be discharged by
the actual Fourier proof before the final no-premise root can use it.
-/
theorem noUniformDiskBound_of_runningLower (hlower : RunningLowerBound) :
    NoUniformDiskBound := by
  intro A
  rintro ⟨B, hB⟩
  rcases A.finite_or_infinite with hA | hA
  · exact not_uniformDiskBound_of_finite hA B hB
  · have hadm := admissible_of_infinite_of_uniformDiskBound hA hB
    rcases hlower with ⟨c, hc, R₀, _hR₀, hlarge⟩
    let t : ℝ := max (|R₀| + 1) ((|B| + 1) / c)
    have htR : |R₀| + 1 ≤ t := le_max_left _ _
    have htB : (|B| + 1) / c ≤ t := le_max_right _ _
    have ht : 0 ≤ t := by nlinarith [abs_nonneg R₀]
    have hscale : R₀ ≤ t ^ 2 := by nlinarith [le_abs_self R₀, abs_nonneg R₀]
    obtain ⟨x, r, hr, _hrscale, herr⟩ := hlarge (t ^ 2) hscale A hadm
    rw [Real.sqrt_sq ht] at herr
    have hbound := (hB x r hr.le).2
    have hct : |B| + 1 ≤ t * c := (div_le_iff₀ hc).mp htB
    nlinarith [le_abs_self B]

end DiskDiscrepancy
