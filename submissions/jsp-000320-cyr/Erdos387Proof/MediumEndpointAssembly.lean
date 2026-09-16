import Erdos387Proof.MediumEndpointError
import Erdos387Proof.MediumComplementMass
import Erdos387Proof.MediumFactorGeometry

/-! Sum the finite harmonic endpoint errors over the actual complementary
vectors. Only these nonnegative errors are enlarged. -/

namespace Erdos387Proof.MediumEndpointAssembly

open Erdos387 MediumFactorWindow MediumFactorGeometry MediumComplementGrouping
open MediumComplementMass MediumEndpointError
open scoped BigOperators

theorem endpoint_base_le {M D A medium X : ℕ} {mass : ℝ}
    (hM : 0 < M) (hD : 0 < D) (hm : 0 < medium)
    (hmA : medium ≤ A) (hX : mass ≤ 4 * X) :
    4 * mass / ((M : ℝ) * D * A) ≤
      (16 * (X : ℝ) / M / medium) * (1 / D) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmR : (0 : ℝ) < medium := by exact_mod_cast hm
  have hAR : (0 : ℝ) < A := hmR.trans_le (by exact_mod_cast hmA)
  calc
    _ ≤ 16 * (X : ℝ) / ((M : ℝ) * D * A) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ 16 * (X : ℝ) / ((M : ℝ) * D * medium) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmA) (by positivity)
    _ = _ := by field_simp

/-- An explicit envelope for one distinguished coordinate. Squarefreeness
and the prime-factor budget are finite arithmetic properties of the actual
retained complementary vectors. -/
theorem sum_endpointErrors_le {B K X z medium large L W : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (i : Fin S.k) (P : Finset ℕ)
    (hz : 1 ≤ z) (hm : 0 < medium)
    (hP : ∀ p ∈ P, p.Prime) (hPz : P ⊆ Finset.range z)
    (hD : ∀ c : {a // a ∈ vectors S X z medium large i},
      Squarefree ((representative c).val.otherValue i))
    (hDW : ∀ c : {a // a ∈ vectors S X z medium large i},
      ((representative c).val.otherValue i).primeFactors.card ≤ W)
    {mass : ℝ} (hmass : 0 ≤ mass) (hX : mass ≤ 4 * X) :
    (∑ c ∈ (vectors S X z medium large i).attach,
      ∑ T ∈ P.powerset, if T.card ≤ L then
        MediumZeroMode.endpointError (∏ p ∈ T, p)
          (CoverBPZ.refinementModulus S * (representative c).val.otherValue i) S.k
          (lower B X ((representative c).val.otherValue i) medium) mass else 0) ≤
      (16 * (X : ℝ) / CoverBPZ.refinementModulus S / medium) *
        (CoverBPZ.refinementModulus S).divisors.card *
          ((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * (2 : ℝ)^W * (4 * (S.k : ℝ))^L *
            roughReciprocalMass z X ^ (S.k - 1) := by
  classical
  let C : ℝ := (16 * (X : ℝ) / CoverBPZ.refinementModulus S / medium) *
        (CoverBPZ.refinementModulus S).divisors.card *
          ((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * (2 : ℝ)^W * (4 * (S.k : ℝ))^L
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have heach (c : {a // a ∈ vectors S X z medium large i}) :
      (∑ T ∈ P.powerset, if T.card ≤ L then
        MediumZeroMode.endpointError (∏ p ∈ T, p)
          (CoverBPZ.refinementModulus S * (representative c).val.otherValue i) S.k
          (lower B X ((representative c).val.otherValue i) medium) mass else 0) ≤
      C * (1 / ((representative c).val.otherValue i : ℝ)) := by
    have hb := endpoint_base_le
      (A := lower B X ((representative c).val.otherValue i) medium)
      (CoverBPZ.refinementModulus_pos S)
      ((representative c).val.otherValue_pos i) hm (le_max_left _ _) hX
    have hsum := sum_endpointError_le (M := CoverBPZ.refinementModulus S) (L := L)
      hP hPz hz (hD c) (hDW c)
      (show 1 ≤ S.k from by have := S.hk3; omega)
      (lower_pos (B := B) (X := X) (D := (representative c).val.otherValue i) hm) hmass
    apply hsum.trans
    have hmul := mul_le_mul_of_nonneg_right hb
      (show (0 : ℝ) ≤ (CoverBPZ.refinementModulus S).divisors.card *
        ((L + 1 : ℕ) : ℝ) * (z : ℝ)^L * (2 : ℝ)^W * (4 * (S.k : ℝ))^L by positivity)
    simpa only [C, mul_assoc, mul_comm, mul_left_comm] using hmul
  calc
    _ ≤ ∑ c ∈ (vectors S X z medium large i).attach,
        C * (1 / ((representative c).val.otherValue i : ℝ)) :=
      Finset.sum_le_sum (fun c _ => heach c)
    _ = C * ∑ c ∈ (vectors S X z medium large i).attach,
        (1 / ((representative c).val.otherValue i : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_reciprocal_representatives_le i) hC

end Erdos387Proof.MediumEndpointAssembly
