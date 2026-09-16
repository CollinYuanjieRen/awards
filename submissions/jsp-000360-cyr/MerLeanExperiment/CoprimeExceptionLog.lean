import MerLeanExperiment.CoprimeExceptions
import MerLeanExperiment.PrimeFactorLog
import Mathlib.Tactic

namespace Erdos441

/-- A logarithmic bound for the actual integers in a signed interval that are
not coprime to a positive integer all of whose prime factors are at least `z`. -/
theorem coprime_exception_log_bound (D : ℕ) (hD : 0 < D) (a b : ℤ) (hab : a ≤ b)
    (z : ℝ) (hz : 1 < z) (hrough : ∀ p ∈ D.primeFactors, z ≤ (p : ℝ)) :
    (({x ∈ Finset.Ioc a b | ¬ Nat.Coprime (x : ℤ).natAbs D}).card : ℝ) * Real.log z ≤
      Real.log D * (((b - a : ℤ) : ℝ) / z + 1) := by
  let bad : Finset ℤ := {x ∈ Finset.Ioc a b | ¬ Nat.Coprime x.natAbs D}
  let B : ℝ := ((b - a : ℤ) : ℝ) / z + 1
  have hcountQ := coprime_exception_bound D hD.ne' a b hab
  have hcountR : (bad.card : ℝ) ≤
      ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) := by
    exact_mod_cast hcountQ
  have hlength : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hzpos : (0 : ℝ) < z := by linarith
  have hterm (p : ℕ) (hp : p ∈ D.primeFactors) :
      (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) ≤ B := by
    have hpz : z ≤ (p : ℝ) := hrough p hp
    dsimp [B]
    gcongr
  have hbad : (bad.card : ℝ) ≤ (D.primeFactors.card : ℝ) * B := by
    calc
      (bad.card : ℝ) ≤
          ∑ p ∈ D.primeFactors, (((b - a : ℤ) : ℝ) / (p : ℝ) + 1) := hcountR
      _ ≤ ∑ _p ∈ D.primeFactors, B :=
        Finset.sum_le_sum fun p hp ↦ hterm p hp
      _ = (D.primeFactors.card : ℝ) * B := by simp
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz.le
  have hfactor := prime_factor_log_bound D hD z hz hrough
  change (bad.card : ℝ) * Real.log z ≤ Real.log D * B
  calc
    (bad.card : ℝ) * Real.log z ≤
        ((D.primeFactors.card : ℝ) * B) * Real.log z :=
      mul_le_mul_of_nonneg_right hbad hlog
    _ = ((D.primeFactors.card : ℝ) * Real.log z) * B := by ring
    _ ≤ Real.log D * B := mul_le_mul_of_nonneg_right hfactor hB

end Erdos441
