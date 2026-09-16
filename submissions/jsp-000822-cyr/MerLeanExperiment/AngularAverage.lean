import MerLeanExperiment.AngularEnergy
import MerLeanExperiment.OscillatorIntegral

open Set

namespace DiskDiscrepancy

/-- The generic integrated-square oscillator estimate instantiated by the
actual angular kernel and its primitive. -/
theorem angularPrimitive_square_integral_lower {z : ℝ} (hz : 128 ≤ z) :
    z ^ 2 / 128 ≤ ∫ t in 0..z, angularPrimitive t ^ 2 := by
  have hu_cont : ContinuousOn angularU (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_angularU ht).continuousAt.continuousWithinAt
  have hv_cont : ContinuousOn angularV (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_angularV ht).continuousAt.continuousWithinAt
  apply oscillator_integral_sq_lower hu_cont hv_cont continuous_angularPrimitive
    (fun _ ht ↦ hasDerivAt_angularU ht)
  · intro t ht
    simpa only [oscillatorCoeff] using hasDerivAt_angularV ht
  · exact fun t ht ↦ angular_energy_bounds ht
  · exact fun t ht ↦ angularPrimitive_eq_sqrt_mul ht
  · exact hz

end DiskDiscrepancy
