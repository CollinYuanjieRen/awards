import MerLeanExperiment.AngularPrimitive
import MerLeanExperiment.OscillatorEnergy

namespace DiskDiscrepancy

/-- The generic energy lemma instantiated by the actual normalized angular integral.
No differential equation or initial-value hypothesis remains. -/
theorem angular_energy_bounds {t : ℝ} (ht : 1 ≤ t) :
    1 / 4 ≤ angularU t ^ 2 + angularV t ^ 2 ∧
      angularU t ^ 2 + angularV t ^ 2 ≤ 7 / 2 := by
  exact oscillator_energy_bounds
    (fun _ ht ↦ hasDerivAt_angularU ht)
    (fun _ ht ↦ hasDerivAt_angularV ht)
    angularU_one_sq_bounds.1 angularU_one_sq_bounds.2 angularV_one_sq_le t ht

theorem continuous_angularPrimitive : Continuous angularPrimitive := by
  have heq : angularPrimitive = fun z ↦ -z * angularKernelDeriv z :=
    funext angularPrimitive_eq_neg_mul_deriv
  rw [heq]
  exact continuous_id.neg.mul continuous_angularKernelDeriv

end DiskDiscrepancy
