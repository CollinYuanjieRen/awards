import MerLeanExperiment.CoprimeExceptionLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos441

/-- Uniformly, rough positive integers of polynomial size have vanishingly few
non-coprime integers in any translated interval of square-root length. -/
theorem eventually_rough_coprime_exceptions (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ x : ℝ in Filter.atTop, ∀ D : ℕ, 0 < D →
    (D : ℝ) ≤ x ^ C → (∀ p ∈ D.primeFactors, Real.log x / K ≤ (p : ℝ)) →
    ∀ a b : ℤ, a ≤ b → ((b - a : ℤ) : ℝ) ≤ C * Real.sqrt x →
    (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) ≤
      ε * Real.sqrt x := by
  let A : ℝ := C * (C * K + 2)
  let X : ℝ := Real.exp (K * Real.exp (A / ε + 1))
  filter_upwards [Filter.eventually_ge_atTop X] with x hx
  intro D hD hDsize hrough a b hab hlength
  let z : ℝ := Real.log x / K
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hinner : 0 < K * Real.exp (A / ε + 1) := by positivity
  have hXone : 1 < X := by
    dsimp [X]
    exact Real.one_lt_exp_iff.mpr hinner
  have hxone : 1 < x := hXone.trans_le hx
  have hxpos : 0 < x := zero_lt_one.trans hxone
  have hlogxpos : 0 < Real.log x := Real.log_pos hxone
  have hlogxLower : K * Real.exp (A / ε + 1) ≤ Real.log x := by
    calc
      K * Real.exp (A / ε + 1) = Real.log X := by simp [X]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx
  have hzLower : Real.exp (A / ε + 1) ≤ z := by
    dsimp [z]
    apply (le_div_iff₀ hK).2
    simpa [mul_comm] using hlogxLower
  have hExpOne : 1 < Real.exp (A / ε + 1) := by
    rw [Real.one_lt_exp_iff]
    positivity
  have hzOne : 1 < z := hExpOne.trans_le hzLower
  have hlogzLower : A / ε + 1 ≤ Real.log z := by
    calc
      A / ε + 1 = Real.log (Real.exp (A / ε + 1)) := by simp
      _ ≤ Real.log z := Real.log_le_log (Real.exp_pos _) hzLower
  have hAthresh : A ≤ ε * Real.log z := by
    have hmul := mul_le_mul_of_nonneg_left hlogzLower hε.le
    have hcancel : ε * (A / ε) = A := by field_simp
    nlinarith
  have hfinite := coprime_exception_log_bound D hD a b hab z hzOne hrough
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hlogD : Real.log D ≤ C * Real.log x := by
    calc
      Real.log D ≤ Real.log (x ^ C) := Real.log_le_log hDreal hDsize
      _ = C * Real.log x := Real.log_rpow hxpos C
  have hzpos : 0 < z := zero_lt_one.trans hzOne
  have hlenNonneg : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hab
  have hsqrtNonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hBnonneg : 0 ≤ ((b - a : ℤ) : ℝ) / z + 1 := by positivity
  have hBbound : ((b - a : ℤ) : ℝ) / z + 1 ≤
      C * Real.sqrt x / z + 1 := by
    gcongr
  have hClogNonneg : 0 ≤ C * Real.log x :=
    mul_nonneg hC.le hlogxpos.le
  have hweighted :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) := by
    calc
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ Real.log D * (((b - a : ℤ) : ℝ) / z + 1) := hfinite
      _ ≤ (C * Real.log x) * (((b - a : ℤ) : ℝ) / z + 1) :=
        mul_le_mul_of_nonneg_right hlogD hBnonneg
      _ ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) :=
        mul_le_mul_of_nonneg_left hBbound hClogNonneg
  have halgebra : (C * Real.log x) * (C * Real.sqrt x / z + 1) =
      C * (C * K * Real.sqrt x + Real.log x) := by
    dsimp [z]
    field_simp [hK.ne', hlogxpos.ne']
  have hlogsqrt := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hxpos)
  rw [Real.log_sqrt hxpos.le] at hlogsqrt
  have hlogSqrt : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have hconstant : C * (C * K * Real.sqrt x + Real.log x) ≤
      A * Real.sqrt x := by
    have hi : C * K * Real.sqrt x + Real.log x ≤
        (C * K + 2) * Real.sqrt x := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hi hC.le
    calc
      C * (C * K * Real.sqrt x + Real.log x) ≤
          C * ((C * K + 2) * Real.sqrt x) := this
      _ = A * Real.sqrt x := by simp [A]; ring
  have hweightedA :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ A * Real.sqrt x := by
    calc
      _ ≤ (C * Real.log x) * (C * Real.sqrt x / z + 1) := hweighted
      _ = C * (C * K * Real.sqrt x + Real.log x) := halgebra
      _ ≤ A * Real.sqrt x := hconstant
  have hproduct :
      (({n ∈ Finset.Ioc a b | ¬ Nat.Coprime (n : ℤ).natAbs D}).card : ℝ) *
          Real.log z ≤ (ε * Real.sqrt x) * Real.log z := by
    calc
      _ ≤ A * Real.sqrt x := hweightedA
      _ ≤ (ε * Real.log z) * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hAthresh hsqrtNonneg
      _ = (ε * Real.sqrt x) * Real.log z := by ring
  exact le_of_mul_le_mul_right hproduct (Real.log_pos hzOne)

end Erdos441
