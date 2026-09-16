import Erdos387Proof.MediumFactorGeometry
import Erdos387Proof.MediumComplementMass
import Erdos387Proof.MediumSignedMainTerm

/-! Uniform main-term bound on the actual complementary-vector cover.
The Brun polynomial stays signed until its proved nonnegativity is used. -/

namespace Erdos387Proof.MediumMainTermAssembly

open Erdos387 MediumFactorWindow MediumFactorGeometry MediumComplementGrouping
open MediumComplementMass MediumSignedMainTerm
open scoped BigOperators

theorem prefactor_le_reciprocal_complement {B X D M medium large : ℕ}
    (hB : 0 < B) (hD : 0 < D) (hM : 0 < M) (hm : 0 < medium)
    (hX : 0 < X)
    (hAU : lower B X D medium ≤ upper X D large) :
    prefactor (M * D) (lower B X D medium) (upper X D large) (3 * X + 1) ≤
      (4 * (X : ℝ) / M) * Real.log (6 * (B : ℝ)) * (1 / D) := by
  have hA : (0 : ℝ) < lower B X D medium := by exact_mod_cast lower_pos hm
  have hU : (0 : ℝ) < upper X D large :=
    hA.trans_le (by exact_mod_cast hAU)
  have hQ : (0 : ℝ) < (M * D : ℕ) := by exact_mod_cast Nat.mul_pos hM hD
  have hlog : 0 ≤ Real.log ((upper X D large : ℝ) / lower B X D medium) :=
    Real.log_nonneg ((one_le_div hA).mpr (by exact_mod_cast hAU))
  have hlogB : 0 ≤ Real.log (6 * (B : ℝ)) := by
    apply Real.log_nonneg
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have ht : (Nat.totient (M * D) : ℝ) / (M * D : ℕ) ≤ 1 :=
    (div_le_one hQ).mpr (by exact_mod_cast Nat.totient_le (M * D))
  have hl : Real.log ((upper X D large : ℝ) / lower B X D medium) ≤
      Real.log (6 * (B : ℝ)) :=
    Real.log_le_log (div_pos hU hA) (upper_div_lower_le hB hD hm)
  have hmass : (3 * (X : ℝ) + 1) ≤ 4 * X := by
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    linarith
  unfold prefactor
  calc
    _ ≤ ((3 * (X : ℝ) + 1) / (M * D : ℕ)) *
        Real.log ((upper X D large : ℝ) / lower B X D medium) := by
      apply mul_le_mul_of_nonneg_right _ hlog
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht
        (show 0 ≤ (3 * (X : ℝ) + 1) / (M * D : ℕ) by positivity)
    _ ≤ ((3 * (X : ℝ) + 1) / (M * D : ℕ)) * Real.log (6 * (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ ((4 * (X : ℝ)) / (M * D : ℕ)) * Real.log (6 * (B : ℝ)) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmass hQ.le) hlogB
    _ = _ := by push_cast; simp only [div_eq_mul_inv, mul_inv]; ring

/-- Main term for one distinguished coordinate, with all actual retained
complement conditions discharged before applying the positive mass bound. -/
theorem sum_mainTerms_le {B K X z medium large L : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (i : Fin S.k)
    (hB : 0 < B) (hX : 0 < X) (hm : 0 < medium) (hL : Even L) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      prefactor (CoverBPZ.refinementModulus S * (representative c).val.otherValue i)
          (lower B X ((representative c).val.otherValue i) medium)
          (upper X ((representative c).val.otherValue i) large) (3 * X + 1) *
        brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (MediumSieveEuler.alpha S.k) L) ≤
      (4 * (X : ℝ) / CoverBPZ.refinementModulus S) * Real.log (6 * (B : ℝ)) *
        brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (MediumSieveEuler.alpha S.k) L *
          roughReciprocalMass z X ^ (S.k - 1) := by
  classical
  let U := brunSubsetSum (MediumSieveEuler.windowPrimes S.k z) (MediumSieveEuler.alpha S.k) L
  have hb := MediumSieveEuler.brun_window_bounds S.k z hL
  have hU : 0 ≤ U := hb.1.le.trans hb.2.1
  let C : ℝ := (4 * (X : ℝ) / CoverBPZ.refinementModulus S) *
    Real.log (6 * (B : ℝ)) * U
  have hC : 0 ≤ C := by
    have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hl : 0 ≤ Real.log (6 * (B : ℝ)) := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg (by positivity) hl) hU
  calc
    _ ≤ ∑ c ∈ (vectors S X z medium large i).attach,
        C * (1 / ((representative c).val.otherValue i : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      have hself : representative c ∈ fibre (representative c) i z medium large :=
        Finset.mem_filter.mpr ⟨representative_mem c, by simp⟩
      have hfac := factor_mem_of_mem_fibre (representative c) (representative c) i hB hself
      have hAU := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hfac).1)
      have hp := prefactor_le_reciprocal_complement hB
        ((representative c).val.otherValue_pos i) (CoverBPZ.refinementModulus_pos S)
        hm hX (hAU.1.le.trans hAU.2)
      simpa only [C, U, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hp hU
    _ = C * ∑ c ∈ (vectors S X z medium large i).attach,
        (1 / ((representative c).val.otherValue i : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_reciprocal_representatives_le i) hC

end Erdos387Proof.MediumMainTermAssembly
