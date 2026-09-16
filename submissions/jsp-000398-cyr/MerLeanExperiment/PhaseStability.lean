import MerLeanExperiment.Subdivision

namespace Erdos492Real

noncomputable section

/-- A small perturbation, modulo an integer, preserves either side of a phase
threshold when the original phase is separated from both cell endpoints and
the threshold. All separation assumptions are explicit local hypotheses. -/
theorem fract_threshold_stable {u v θ δ : ℝ} (z : ℤ)
    (herror : |v - u - z| < δ)
    (hleft : δ ≤ Int.fract u) (hright : Int.fract u ≤ 1 - δ)
    (hthreshold : δ ≤ |Int.fract u - θ|) :
    (Int.fract v < θ ↔ Int.fract u < θ) := by
  have herr := abs_lt.mp herror
  have hidentity := Int.fract_add_floor u
  have hfloor : ⌊v - (z : ℝ)⌋ = ⌊u⌋ := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  have hphase : Int.fract v = v - z - (⌊u⌋ : ℝ) := by
    rw [← Int.fract_sub_intCast v z]
    change v - z - (⌊v - (z : ℝ)⌋ : ℝ) = _
    rw [hfloor]
  rw [hphase]
  rcases le_total (Int.fract u) θ with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hthreshold
    constructor <;> intro hh <;> linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hthreshold
    constructor <;> intro hh <;> linarith

/-- The logarithmic phase perturbation supplied by simultaneous approximation. -/
theorem logarithmic_phase_error (q : ℕ) {m x δ : ℝ} (z : ℤ)
    (hm : 0 < m) (hx : 0 < x)
    (happrox : |(q : ℝ) * Real.log m - z| < δ) :
    |(q : ℝ) * Real.log (m * x) - (q : ℝ) * Real.log x - z| < δ := by
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hx)]
  convert happrox using 1
  congr 1
  ring

end

end Erdos492Real
