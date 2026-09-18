import MerLeanExperiment.AlgebraicSetup
import Mathlib.RingTheory.PowerSeries.Log

/-!
# Truncated exponential factorization

This file formalizes the objects and exact statement faces in
Luo--Yang--Zhu Lemma 2.1.  The perturbation series is `exp(-D)`, where `D`
contains power sums of degrees `2` through `n+1`.
-/

open Finset PowerSeries

namespace Erdos973

/-- `D_n(t) = sum_{k=2}^{n+1} p_k t^k/k` as a power series. -/
noncomputable def perturbationExponent {n : ℕ} (z : Fin n → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k =>
    if k ∈ Finset.Icc 2 (n + 1) then powerSum z k / (k : ℂ) else 0

/-- `A_n(t) = exp(-D_n(t))`. -/
noncomputable def perturbationSeries {n : ℕ} (z : Fin n → ℂ) : PowerSeries ℂ :=
  (PowerSeries.exp ℂ).subst (-(perturbationExponent z))

/-- The coefficient `d_{ell,n}` of the perturbation series. -/
noncomputable def perturbationCoeff {n : ℕ} (z : Fin n → ℂ) (ell : ℕ) : ℂ :=
  PowerSeries.coeff ell (perturbationSeries z)

/-- The scalar majorant `b_n(R)`. -/
noncomputable def perturbationMajorant (n : ℕ) (R : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n + 1), R ^ k / k

theorem perturbationCoeff_zero {n : ℕ} (z : Fin n → ℂ) :
    perturbationCoeff z 0 = 1 := by
  have hconst : PowerSeries.constantCoeff (-(perturbationExponent z)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [perturbationExponent]
  have hsubst : PowerSeries.HasSubst (-(perturbationExponent z)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  have hD : PowerSeries.constantCoeff (perturbationExponent z) = 0 := by
    simpa using hconst
  rw [perturbationCoeff, perturbationSeries,
    PowerSeries.coeff_subst' hsubst]
  simp only [PowerSeries.coeff_exp]
  rw [finsum_eq_single _ 0 (fun d hd ↦ by simp [hd, hD])]
  simp

theorem perturbationCoeff_one {n : ℕ} (z : Fin n → ℂ) :
    perturbationCoeff z 1 = 0 := by
  have hconst : PowerSeries.constantCoeff (-(perturbationExponent z)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [perturbationExponent]
  have hone : PowerSeries.coeff 1 (-(perturbationExponent z)) = 0 := by
    simp [perturbationExponent]
  have hsubst : PowerSeries.HasSubst (-(perturbationExponent z)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  rw [perturbationCoeff, perturbationSeries,
    PowerSeries.coeff_subst' hsubst]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  simp [PowerSeries.coeff_exp, PowerSeries.coeff_one_pow, hconst, hone]

private noncomputable def geometricSeries (a : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦ a ^ k

private theorem one_sub_mul_geometricSeries (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * geometricSeries a = 1 := by
  ext k
  cases k with
  | zero => simp [sub_mul, geometricSeries]
  | succ k => simp [sub_mul, mul_assoc, geometricSeries, pow_succ']

private noncomputable def powerSumSeries {n : ℕ} (z : Fin n → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦ -powerSum z (k + 1)

private theorem powerSumSeries_eq_sum_geometric {n : ℕ} (z : Fin n → ℂ) :
    powerSumSeries z = ∑ j, -(PowerSeries.C (z j) * geometricSeries (z j)) := by
  ext k
  simp [powerSumSeries, geometricSeries, powerSum, pow_succ']

private theorem rootProduct_mul_geometricSeries {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    (rootProduct z : PowerSeries ℂ) * geometricSeries (z j) =
      ∏ i ∈ Finset.univ.erase j,
        (1 - PowerSeries.C (z i) * PowerSeries.X) := by
  have hcoe : (rootProduct z : PowerSeries ℂ) =
      ∏ i, (1 - PowerSeries.C (z i) * PowerSeries.X) := by
    rw [rootProduct]
    change Polynomial.coeToPowerSeries.ringHom
      (∏ i, (1 - Polynomial.C (z i) * Polynomial.X)) = _
    rw [map_prod]
    simp
  rw [hcoe]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i ↦ (1 - PowerSeries.C (z i) * PowerSeries.X)) (Finset.mem_univ j)]
  simp only [mul_assoc, one_sub_mul_geometricSeries, mul_one]

private theorem rootProduct_mul_powerSumSeries {n : ℕ} (z : Fin n → ℂ) :
    (rootProduct z : PowerSeries ℂ) * powerSumSeries z =
      d⁄dX ℂ (rootProduct z : PowerSeries ℂ) := by
  rw [powerSumSeries_eq_sum_geometric, Finset.mul_sum]
  calc
    ∑ j, (rootProduct z : PowerSeries ℂ) *
        -(PowerSeries.C (z j) * geometricSeries (z j)) =
        ∑ j, -(PowerSeries.C (z j) *
          ((rootProduct z : PowerSeries ℂ) * geometricSeries (z j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = ∑ j, -(PowerSeries.C (z j) *
          ∏ i ∈ Finset.univ.erase j,
            (1 - PowerSeries.C (z i) * PowerSeries.X)) := by
            simp_rw [rootProduct_mul_geometricSeries]
  rw [PowerSeries.derivative_coe, rootProduct, Polynomial.derivative_prod_finset]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    zero_sub, zero_mul, mul_one, zero_add]
  rw [show (↑(∑ x, (∏ b ∈ Finset.univ.erase x,
      (1 - Polynomial.C (z b) * Polynomial.X)) * -Polynomial.C (z x)) :
      PowerSeries ℂ) = ∑ x, (∏ b ∈ Finset.univ.erase x,
        (1 - PowerSeries.C (z b) * PowerSeries.X)) * -PowerSeries.C (z x) by
          change Polynomial.coeToPowerSeries.ringHom (∑ x,
            (∏ b ∈ Finset.univ.erase x,
              (1 - Polynomial.C (z b) * Polynomial.X)) * -Polynomial.C (z x)) = _
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [map_mul, map_neg, map_prod]
          simp]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private noncomputable def comparisonSeries {n : ℕ} (z : Fin n → ℂ) : PowerSeries ℂ :=
  perturbationSeries z * PowerSeries.rescale (-powerSum z 1) (PowerSeries.exp ℂ)

private theorem coeff_comparisonSeries {n : ℕ} (z : Fin n → ℂ) (m : ℕ) :
    PowerSeries.coeff m (comparisonSeries z) =
      ∑ ell ∈ Finset.range (m + 1),
        perturbationCoeff z ell *
          (-powerSum z 1) ^ (m - ell) / ((m - ell).factorial : ℂ) := by
  simp [comparisonSeries, perturbationCoeff, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro ell hell
  ring

private theorem derivative_rescale_exp (a : ℂ) :
    d⁄dX ℂ (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
      PowerSeries.C a * PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  ext k
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, PowerSeries.coeff_C_mul]
  rw [Nat.factorial_succ, pow_succ']
  push_cast
  field_simp

private theorem derivative_comparisonSeries {n : ℕ} (z : Fin n → ℂ) :
    d⁄dX ℂ (comparisonSeries z) = comparisonSeries z *
      (PowerSeries.C (-powerSum z 1) + d⁄dX ℂ (-(perturbationExponent z))) := by
  have hconst : PowerSeries.constantCoeff (-(perturbationExponent z)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [perturbationExponent]
  have hsubst : PowerSeries.HasSubst (-(perturbationExponent z)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  rw [comparisonSeries, perturbationSeries, Derivation.leibniz,
    PowerSeries.derivative_subst hsubst, PowerSeries.derivative_exp,
    derivative_rescale_exp]
  ring

private theorem coeff_logDerivative_comparisonSeries {n : ℕ} (z : Fin n → ℂ)
    (k : ℕ) (hk : k ≤ n) :
    PowerSeries.coeff k
      (PowerSeries.C (-powerSum z 1) + d⁄dX ℂ (-(perturbationExponent z))) =
        PowerSeries.coeff k (powerSumSeries z) := by
  cases k with
  | zero =>
      simp [powerSumSeries, perturbationExponent]
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_derivative]
      simp [perturbationExponent]
  | succ k =>
      have hmem : k + 1 + 1 ∈ Finset.Icc 2 (n + 1) := by
        simp only [Finset.mem_Icc]
        omega
      simp only [map_add, PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false,
        zero_add, PowerSeries.coeff_derivative, map_neg,
        powerSumSeries, PowerSeries.coeff_mk, perturbationExponent, hmem]
      push_cast
      have hne : (↑k + 1 + 1 : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero (k + 1))
      field_simp
      simp

private theorem rootProduct_coeff_eq_comparisonSeries {n m : ℕ}
    (z : Fin n → ℂ) (hm : m ≤ n + 1) :
    PowerSeries.coeff m (rootProduct z : PowerSeries ℂ) =
      PowerSeries.coeff m (comparisonSeries z) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero =>
          rw [coeff_comparisonSeries]
          rw [Polynomial.coeff_coe]
          simp [rootProduct, perturbationCoeff_zero,
            Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
      | succ m =>
          have hmn : m ≤ n := by omega
          have hroot := congrArg (PowerSeries.coeff m)
            (rootProduct_mul_powerSumSeries z)
          have hcomp := congrArg (PowerSeries.coeff m)
            (derivative_comparisonSeries z)
          rw [PowerSeries.coeff_derivative] at hroot hcomp
          have hproducts : PowerSeries.coeff m
                ((rootProduct z : PowerSeries ℂ) * powerSumSeries z) =
              PowerSeries.coeff m
                (comparisonSeries z *
                  (PowerSeries.C (-powerSum z 1) +
                    d⁄dX ℂ (-(perturbationExponent z)))) := by
            simp only [PowerSeries.coeff_mul]
            apply Finset.sum_congr rfl
            intro ij hij
            have hijsum : ij.1 + ij.2 = m := mem_antidiagonal.mp hij
            rw [ih ij.1 (by omega) (by omega),
              coeff_logDerivative_comparisonSeries z ij.2 (by omega)]
          rw [hroot] at hproducts
          rw [← hcomp] at hproducts
          exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m) hproducts

/-- Coefficient comparison in `F_n(t) = exp(x_n t) A_n(t)` through degree
`n+1`, where `x_n = -p_1`. -/
theorem rootProduct_coeff_eq_truncated_convolution {n m : ℕ}
    (z : Fin n → ℂ) (hm : m ≤ n + 1) :
    (rootProduct z).coeff m =
      ∑ ell ∈ Finset.range (m + 1),
        perturbationCoeff z ell *
          (-powerSum z 1) ^ (m - ell) / ((m - ell).factorial : ℂ) := by
  rw [← coeff_comparisonSeries]
  simpa using rootProduct_coeff_eq_comparisonSeries z hm

private noncomputable def weightedCoeff (f : PowerSeries ℂ) (R : ℝ) (k : ℕ) : ℝ :=
  ‖PowerSeries.coeff k f‖ * |R| ^ k

private noncomputable def weightedCoeffSum (f : PowerSeries ℂ) (R : ℝ) : ℝ :=
  ∑' k, weightedCoeff f R k

private theorem weightedCoeff_nonneg (f : PowerSeries ℂ) (R : ℝ) (k : ℕ) :
    0 ≤ weightedCoeff f R k := by
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)

private theorem weightedCoeff_mul_le (f g : PowerSeries ℂ) (R : ℝ) (k : ℕ) :
    weightedCoeff (f * g) R k ≤
      ∑ ij ∈ antidiagonal k, weightedCoeff f R ij.1 * weightedCoeff g R ij.2 := by
  rw [weightedCoeff, PowerSeries.coeff_mul]
  calc
    ‖∑ ij ∈ antidiagonal k,
        PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g‖ * |R| ^ k ≤
        (∑ ij ∈ antidiagonal k,
          ‖PowerSeries.coeff ij.1 f * PowerSeries.coeff ij.2 g‖) * |R| ^ k := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ (∑ ij ∈ antidiagonal k,
          ‖PowerSeries.coeff ij.1 f‖ * ‖PowerSeries.coeff ij.2 g‖) * |R| ^ k := by
            gcongr with ij hij
            exact norm_mul_le _ _
    _ = ∑ ij ∈ antidiagonal k,
          weightedCoeff f R ij.1 * weightedCoeff g R ij.2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro ij hij
            rw [weightedCoeff, weightedCoeff, ← mem_antidiagonal.mp hij, pow_add]
            ring

private theorem summable_weightedCoeff_mul {f g : PowerSeries ℂ} {R : ℝ}
    (hf : Summable (weightedCoeff f R)) (hg : Summable (weightedCoeff g R)) :
    Summable (weightedCoeff (f * g) R) := by
  have hconv : Summable (fun k ↦
      ∑ ij ∈ antidiagonal k, weightedCoeff f R ij.1 * weightedCoeff g R ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (hf.mul_of_nonneg hg (weightedCoeff_nonneg f R) (weightedCoeff_nonneg g R))
  exact hconv.of_nonneg_of_le (weightedCoeff_nonneg _ _) (weightedCoeff_mul_le f g R)

private theorem weightedCoeffSum_mul_le {f g : PowerSeries ℂ} {R : ℝ}
    (hf : Summable (weightedCoeff f R)) (hg : Summable (weightedCoeff g R)) :
    weightedCoeffSum (f * g) R ≤ weightedCoeffSum f R * weightedCoeffSum g R := by
  have hprod := hf.mul_of_nonneg hg (weightedCoeff_nonneg f R) (weightedCoeff_nonneg g R)
  have hconv : Summable (fun k ↦
      ∑ ij ∈ antidiagonal k, weightedCoeff f R ij.1 * weightedCoeff g R ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hprod
  calc
    weightedCoeffSum (f * g) R ≤
        ∑' k, ∑ ij ∈ antidiagonal k,
          weightedCoeff f R ij.1 * weightedCoeff g R ij.2 :=
      (summable_weightedCoeff_mul hf hg).tsum_le_tsum
        (weightedCoeff_mul_le f g R) hconv
    _ = weightedCoeffSum f R * weightedCoeffSum g R := by
      symm
      exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hprod

private theorem summable_weightedCoeff_pow {f : PowerSeries ℂ} {R : ℝ}
    (hf : Summable (weightedCoeff f R)) (d : ℕ) :
    Summable (weightedCoeff (f ^ d) R) := by
  induction d with
  | zero =>
      apply summable_of_ne_finset_zero (s := {0})
      intro k hk
      simp_all [weightedCoeff]
  | succ d ih =>
      rw [pow_succ]
      exact summable_weightedCoeff_mul ih hf

private theorem weightedCoeffSum_pow_le {f : PowerSeries ℂ} {R : ℝ}
    (hf : Summable (weightedCoeff f R)) (d : ℕ) :
    weightedCoeffSum (f ^ d) R ≤ weightedCoeffSum f R ^ d := by
  induction d with
  | zero =>
      rw [weightedCoeffSum, tsum_eq_single 0]
      · simp [weightedCoeff]
      · intro k hk
        simp [weightedCoeff, hk]
  | succ d ih =>
      rw [pow_succ, pow_succ]
      exact (weightedCoeffSum_mul_le (summable_weightedCoeff_pow hf d) hf).trans
        (mul_le_mul_of_nonneg_right ih (tsum_nonneg (weightedCoeff_nonneg f R)))

private theorem summable_weightedCoeff_perturbationExponent {n : ℕ}
    (z : Fin n → ℂ) (R : ℝ) :
    Summable (weightedCoeff (-(perturbationExponent z)) R) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 2 (n + 1))
  intro k hk
  have hcoeff : PowerSeries.coeff k (-(perturbationExponent z)) = 0 := by
    rw [map_neg, perturbationExponent, PowerSeries.coeff_mk, if_neg hk, neg_zero]
  simp [weightedCoeff, hcoeff]

private noncomputable def expSubstMajorantTerm
    (b : PowerSeries ℂ) (R : ℝ) (d k : ℕ) : ℝ :=
  weightedCoeff (b ^ d) R k / d.factorial

private theorem expSubstMajorantTerm_nonneg
    (b : PowerSeries ℂ) (R : ℝ) (d k : ℕ) :
    0 ≤ expSubstMajorantTerm b R d k := by
  exact div_nonneg (weightedCoeff_nonneg _ _ _) (Nat.cast_nonneg _)

private theorem summable_expSubstMajorantTerm_prod
    {b : PowerSeries ℂ} {R : ℝ} (hb : Summable (weightedCoeff b R)) :
    Summable (fun p : ℕ × ℕ ↦ expSubstMajorantTerm b R p.1 p.2) := by
  rw [summable_prod_of_nonneg (fun p ↦ expSubstMajorantTerm_nonneg b R p.1 p.2)]
  constructor
  · intro d
    exact (summable_weightedCoeff_pow hb d).div_const d.factorial
  · have hrow : ∀ d,
        (∑' k, expSubstMajorantTerm b R d k) ≤
          weightedCoeffSum b R ^ d / d.factorial := by
      intro d
      rw [show (∑' k, expSubstMajorantTerm b R d k) =
          weightedCoeffSum (b ^ d) R / d.factorial by
        simp only [expSubstMajorantTerm, weightedCoeffSum]
        rw [tsum_div_const]]
      exact div_le_div_of_nonneg_right (weightedCoeffSum_pow_le hb d)
        (Nat.cast_nonneg _)
    exact (Real.summable_pow_div_factorial (weightedCoeffSum b R)).of_nonneg_of_le
      (fun d ↦ tsum_nonneg (expSubstMajorantTerm_nonneg b R d)) hrow

private theorem weightedCoeff_exp_subst_le
    {b : PowerSeries ℂ} {R : ℝ}
    (hconst : PowerSeries.constantCoeff b = 0)
    (hb : Summable (weightedCoeff b R)) (k : ℕ) :
    weightedCoeff ((PowerSeries.exp ℂ).subst b) R k ≤
      ∑' d, expSubstMajorantTerm b R d k := by
  have hsubst : PowerSeries.HasSubst b :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  let q : ℕ → ℂ := fun d ↦
    PowerSeries.coeff d (PowerSeries.exp ℂ) • PowerSeries.coeff k (b ^ d)
  have hqfin : q.HasFiniteSupport := by
    simpa [q] using
      (PowerSeries.coeff_subst_finite' hsubst (PowerSeries.exp ℂ) k)
  have hq : Summable q := summable_of_hasFiniteSupport hqfin
  have hfin : finsum q = ∑' d, q d :=
    (tsum_eq_finsum (L := .unconditional ℕ) hqfin).symm
  rw [weightedCoeff, PowerSeries.coeff_subst' hsubst]
  change ‖finsum q‖ * |R| ^ k ≤ _
  rw [hfin]
  calc
    ‖∑' d, q d‖ * |R| ^ k ≤ (∑' d, ‖q d‖) * |R| ^ k := by
      gcongr
      exact norm_tsum_le_tsum_norm hq.norm
    _ = ∑' d, ‖q d‖ * |R| ^ k := by rw [tsum_mul_right]
    _ = ∑' d, expSubstMajorantTerm b R d k := by
      apply tsum_congr
      intro d
      simp [q, expSubstMajorantTerm, weightedCoeff, PowerSeries.coeff_exp,
        norm_mul, norm_smul, div_eq_mul_inv]
      ring

private theorem summable_weightedCoeff_exp_subst
    {b : PowerSeries ℂ} {R : ℝ}
    (hconst : PowerSeries.constantCoeff b = 0)
    (hb : Summable (weightedCoeff b R)) :
    Summable (weightedCoeff ((PowerSeries.exp ℂ).subst b) R) := by
  have hprod := summable_expSubstMajorantTerm_prod hb
  have hswap : Summable (fun p : ℕ × ℕ ↦ expSubstMajorantTerm b R p.2 p.1) := by
    rw [← (Equiv.prodComm ℕ ℕ).summable_iff]
    simpa [Function.comp_def] using hprod
  have hmarg : Summable (fun k ↦ ∑' d, expSubstMajorantTerm b R d k) :=
    (summable_prod_of_nonneg
      (fun p ↦ expSubstMajorantTerm_nonneg b R p.2 p.1)).mp hswap |>.2
  exact hmarg.of_nonneg_of_le (weightedCoeff_nonneg _ _)
    (weightedCoeff_exp_subst_le hconst hb)

private theorem weightedCoeffSum_exp_subst_le
    {b : PowerSeries ℂ} {R : ℝ}
    (hconst : PowerSeries.constantCoeff b = 0)
    (hb : Summable (weightedCoeff b R)) :
    weightedCoeffSum ((PowerSeries.exp ℂ).subst b) R ≤
      Real.exp (weightedCoeffSum b R) := by
  have hprod := summable_expSubstMajorantTerm_prod hb
  have hmarg : Summable (fun k ↦ ∑' d, expSubstMajorantTerm b R d k) := by
    have hswap : Summable (fun p : ℕ × ℕ ↦ expSubstMajorantTerm b R p.2 p.1) := by
      rw [← (Equiv.prodComm ℕ ℕ).summable_iff]
      simpa [Function.comp_def] using hprod
    exact (summable_prod_of_nonneg
      (fun p ↦ expSubstMajorantTerm_nonneg b R p.2 p.1)).mp hswap |>.2
  calc
    weightedCoeffSum ((PowerSeries.exp ℂ).subst b) R ≤
        ∑' k, ∑' d, expSubstMajorantTerm b R d k :=
      (summable_weightedCoeff_exp_subst hconst hb).tsum_le_tsum
        (weightedCoeff_exp_subst_le hconst hb) hmarg
    _ = ∑' d, ∑' k, expSubstMajorantTerm b R d k := hprod.tsum_comm
    _ ≤ ∑' d, weightedCoeffSum b R ^ d / d.factorial := by
      have hrows : Summable (fun d ↦ ∑' k, expSubstMajorantTerm b R d k) :=
        (summable_prod_of_nonneg
          (fun p ↦ expSubstMajorantTerm_nonneg b R p.1 p.2)).mp hprod |>.2
      apply hrows.tsum_le_tsum
      · intro d
        rw [show (∑' k, expSubstMajorantTerm b R d k) =
            weightedCoeffSum (b ^ d) R / d.factorial by
          simp only [expSubstMajorantTerm, weightedCoeffSum]
          rw [tsum_div_const]]
        exact div_le_div_of_nonneg_right (weightedCoeffSum_pow_le hb d)
          (Nat.cast_nonneg _)
      · exact Real.summable_pow_div_factorial _
    _ = Real.exp (weightedCoeffSum b R) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Absolute summability of the perturbation coefficients at every real radius. -/
theorem summable_perturbationCoeff_norm_mul_pow {n : ℕ}
    (z : Fin n → ℂ) (R : ℝ) :
    Summable (fun ell ↦ ‖perturbationCoeff z ell‖ * R ^ ell) := by
  have hconst : PowerSeries.constantCoeff (-(perturbationExponent z)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [perturbationExponent]
  have hs : Summable (weightedCoeff (perturbationSeries z) R) := by
    exact summable_weightedCoeff_exp_subst hconst
      (summable_weightedCoeff_perturbationExponent z R)
  apply Summable.of_norm
  convert hs using 1
  ext ell
  simp [weightedCoeff, perturbationCoeff, perturbationSeries,
    Real.norm_eq_abs, abs_mul, abs_pow]

private theorem weightedCoeffSum_perturbationExponent_le {n : ℕ}
    (z : Fin n → ℂ) {epsilon R : ℝ} (hepsilon : 0 ≤ epsilon) (hR : 0 ≤ R)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon) :
    weightedCoeffSum (-(perturbationExponent z)) R ≤
      epsilon * perturbationMajorant n R := by
  rw [weightedCoeffSum, tsum_eq_sum (s := Finset.Icc 2 (n + 1))]
  · calc
      ∑ k ∈ Finset.Icc 2 (n + 1),
          weightedCoeff (-(perturbationExponent z)) R k ≤
          ∑ k ∈ Finset.Icc 2 (n + 1), epsilon * (R ^ k / k) := by
            apply Finset.sum_le_sum
            intro k hk
            simp only [weightedCoeff, map_neg, norm_neg, perturbationExponent,
              PowerSeries.coeff_mk, if_pos hk, abs_of_nonneg hR]
            have hkpos : 0 < (k : ℝ) := by
              exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (Finset.mem_Icc.mp hk).1)
            have hnormk : ‖(k : ℂ)‖ = (k : ℝ) := by simp
            rw [norm_div, hnormk]
            convert mul_le_mul_of_nonneg_right (hsmall k hk)
              (div_nonneg (pow_nonneg hR k) hkpos.le) using 1 <;> ring
      _ = epsilon * perturbationMajorant n R := by
        rw [perturbationMajorant, Finset.mul_sum]
  · intro k hk
    have hcoeff : PowerSeries.coeff k (-(perturbationExponent z)) = 0 := by
      rw [map_neg, perturbationExponent, PowerSeries.coeff_mk, if_neg hk, neg_zero]
    simp [weightedCoeff, hcoeff]

/-- Weighted coefficient majorant from Lemma 2.1. -/
theorem perturbationCoeff_majorant {n : ℕ} (z : Fin n → ℂ)
    {epsilon R : ℝ} (hepsilon : 0 ≤ epsilon) (hR : 0 ≤ R)
    (hsmall : ∀ k ∈ Finset.Icc 2 (n + 1), ‖powerSum z k‖ ≤ epsilon) :
    (∑' ell : ℕ, if 2 ≤ ell then ‖perturbationCoeff z ell‖ * R ^ ell else 0) ≤
      Real.exp (epsilon * perturbationMajorant n R) - 1 := by
  let f : ℕ → ℝ := fun ell ↦ ‖perturbationCoeff z ell‖ * R ^ ell
  have hf : Summable f := summable_perturbationCoeff_norm_mul_pow z R
  have hconst : PowerSeries.constantCoeff (-(perturbationExponent z)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [perturbationExponent]
  have hb := summable_weightedCoeff_perturbationExponent z R
  have hfull : (∑' ell, f ell) ≤
      Real.exp (epsilon * perturbationMajorant n R) := by
    calc
      ∑' ell, f ell = weightedCoeffSum (perturbationSeries z) R := by
        apply tsum_congr
        intro ell
        simp [f, weightedCoeffSum, weightedCoeff, perturbationCoeff,
          abs_of_nonneg hR]
      _ ≤ Real.exp (weightedCoeffSum (-(perturbationExponent z)) R) := by
        exact weightedCoeffSum_exp_subst_le hconst hb
      _ ≤ Real.exp (epsilon * perturbationMajorant n R) :=
        Real.exp_le_exp.mpr
          (weightedCoeffSum_perturbationExponent_le z hepsilon hR hsmall)
  let g : ℕ → ℝ := fun ell ↦ if ell = 0 then 0 else f ell
  have hg : Summable g := by
    exact hf.of_nonneg_of_le
      (fun ell ↦ by simp [g, f]; positivity)
      (fun ell ↦ by
        by_cases h : ell = 0
        · simp [g, h, f]
        · simp [g, h])
  have hsplit0 := hf.tsum_eq_add_tsum_ite 0
  have hsplit1 := hg.tsum_eq_add_tsum_ite 1
  have hrem0 : (fun ell ↦ if ell = 0 then 0 else f ell) = g := rfl
  rw [hrem0] at hsplit0
  have htailfun :
      (fun ell ↦ if ell = 1 then 0 else g ell) =
        (fun ell ↦ if 2 ≤ ell then f ell else 0) := by
    funext ell
    by_cases h0 : ell = 0
    · simp [g, h0]
    by_cases h1 : ell = 1
    · simp [g, h0, h1]
    have h2 : 2 ≤ ell := by omega
    simp [g, h0, h1, h2]
  rw [htailfun] at hsplit1
  have hf0 : f 0 = 1 := by simp [f, perturbationCoeff_zero]
  have hg1 : g 1 = 0 := by simp [g, f, perturbationCoeff_one]
  rw [hf0] at hsplit0
  rw [hg1] at hsplit1
  have htail :
      (∑' ell, if 2 ≤ ell then f ell else 0) = (∑' ell, f ell) - 1 := by
    linarith
  change (∑' ell, if 2 ≤ ell then f ell else 0) ≤ _
  rw [htail]
  linarith

end Erdos973
