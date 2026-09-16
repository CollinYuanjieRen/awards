import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos441

theorem prime_factor_log_bound (D : ℕ) (hD : 0 < D) (z : ℝ) (hz : 1 < z)
    (hrough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ)) :
    (D.primeFactors.card : ℝ) * Real.log z ≤ Real.log D := by
  have hprod : (∏ p ∈ D.primeFactors, (p : ℝ)) ≤ (D : ℝ) := by
    have hn := Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)
    have hc : ((∏ p ∈ D.primeFactors, p : ℕ) : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hn
    simpa only [Nat.cast_prod] using hc
  have hpos (p : ℕ) (hp : p ∈ D.primeFactors) : (0 : ℝ) < p := by
    exact_mod_cast Nat.pos_of_mem_primeFactors hp
  have hprodpos : (0 : ℝ) < ∏ p ∈ D.primeFactors, (p : ℝ) :=
    Finset.prod_pos hpos
  calc
    (D.primeFactors.card : ℝ) * Real.log z =
        ∑ _p ∈ D.primeFactors, Real.log z := by simp
    _ ≤ ∑ p ∈ D.primeFactors, Real.log p := by
      exact Finset.sum_le_sum fun p hp => Real.log_le_log (by linarith) (hrough p hp)
    _ = Real.log (∏ p ∈ D.primeFactors, (p : ℝ)) :=
      (Real.log_prod fun p hp => ne_of_gt (hpos p hp)).symm
    _ ≤ Real.log D := Real.log_le_log hprodpos hprod

end Erdos441

#print axioms Erdos441.prime_factor_log_bound
