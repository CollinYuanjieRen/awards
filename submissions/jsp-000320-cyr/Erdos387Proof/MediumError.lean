import Erdos387Proof.MediumFibreBound
import Erdos387Proof.MediumSubpowerReduction

/-! Actual medium-error counting on the original squarefree candidate
family. All arithmetic hypotheses are discharged on the subpower scale. -/

set_option autoImplicit false

namespace Erdos387Proof.MediumError

open Erdos387 Erdos387.CoverBPZ MediumCertificateCover MediumComplementGrouping
open MediumFourierReduction MediumFibreBound MediumOuterSummation MediumTotalEnvelope
open MediumSubpowerReduction MediumFourierTailDecay Filter
open scoped BigOperators Topology

theorem sum_partialErrors_le {B K X z medium large H L W : ℕ}
    (S : BPZSection6Input B K)
    (hB : 0 < B) (hX : 0 < X) (hm : 0 < medium)
    (hz : 2*S.k ≤ z) (hkX : S.k ≤ X) (hH : 1 ≤ H) (hHX : 4*B*H ≤ X)
    (hW : ∀ i : Fin S.k, ∀ C ∈ certificates S X z medium large i,
      (C.val.otherValue i).primeFactors.card ≤ W) :
    (∑ i : Fin S.k, ∑ c ∈ (vectors S X z medium large i).attach,
      fibrePartialError (representative c) i z L medium large H) ≤
      totalEnvelope S X z medium large L W H := by
  classical
  have hz1 : 1 ≤ z := by have := S.hk3; omega
  apply le_trans _ (sum_completion_multiplicities_le S hB hz1)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro c hc
  unfold fibrePartialError
  apply Finset.sum_le_sum
  intro T hT
  by_cases hTL : T.card ≤ L
  · simp only [if_pos hTL]
    exact abs_sum_partialRemainder_le hB hX hm hz hkX hH hHX
      (representative_mem c) hT hTL (hW i _ (representative_mem c))
  · simp only [if_neg hTL, le_refl]

theorem eventually_totalFourierError_le {B K : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop, totalFourierError S N ≤
      totalEnvelope S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
        (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k) (2*N) (N^2)
        (height N S.k) +
      MediumFourierTail.totalTailEnvelope S.k (refinementModulus S)
        (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) (2*N) (height N S.k) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    SubpowerScale.eventually_const_le_z hk (2*S.k),
    SubpowerScale.eventually_const_le_X hk S.k,
    eventually_four_mul_height_le_X S.k B hk] with N hN hz hkX hHX
  have hm : 0 < SubpowerScale.medium N S.k := by
    unfold SubpowerScale.medium BPZScale.medium SubpowerScale.base
    positivity
  have h1 := sum_fourierError_le_partial_add_tail
    (X := SubpowerScale.X N S.k) (z := SubpowerScale.z N S.k)
    (medium := SubpowerScale.medium N S.k) (large := SubpowerScale.large N S.k)
    (L := 2*N) (H := height N S.k) S hB (SubpowerScale.X_pos N S.k)
    (height_pos N S.k) (SubpowerScale.z_pos N S.k)
  apply h1.trans
  apply add_le_add _ le_rfl
  apply sum_partialErrors_le S hB (SubpowerScale.X_pos N S.k) hm hz hkX
    (height_pos N S.k) hHX
  intro i C hC
  exact MediumComplementBounds.subpower_primeFactors_card_le (by omega) hC

theorem totalFourierError_nonneg {B K : ℕ} (S : BPZSection6Input B K) (N : ℕ) :
    0 ≤ totalFourierError S N := by
  classical
  unfold totalFourierError MediumFiniteReduction.fourierError
  positivity

theorem tendsto_totalFourierError_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => totalFourierError S N / sieveScale S N) atTop (𝓝 0) := by
  have hlim := (tendsto_normalizedTotal_zero S hB).add
    (tendsto_totalTailEnvelope_div_sieveScale_zero S (refinementModulus_pos S))
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall (fun N =>
      div_nonneg (totalFourierError_nonneg S N) (sieveScale_pos S N).le)
  · filter_upwards [eventually_totalFourierError_le S hB] with N hN
    have h := div_le_div_of_nonneg_right hN (sieveScale_pos S N).le
    simpa only [add_div, normalizedTotal, sieveScale] using h

/-- The original squarefree medium-error count vanishes relative to the
same original sieve density as the candidate lower bound. -/
theorem tendsto_medium_card_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N =>
      ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedMediumErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k)).card : ℝ) /
            sieveScale S N) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  have hlim := (tendsto_nonoscillatory_div_sieveScale_zero S).add
    (tendsto_totalFourierError_div_sieveScale_zero S hB)
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall (fun N =>
      div_nonneg (Nat.cast_nonneg _) (sieveScale_pos S N).le)
  · filter_upwards [eventually_ge_atTop (1 : ℕ),
      SubpowerScale.eventually_const_le_z hk (2*S.k)] with N hN hz
    have h := div_le_div_of_nonneg_right (card_medium_le (N := N) S hB (by omega) hz)
      (sieveScale_pos S N).le
    simpa only [add_div] using h

end Erdos387Proof.MediumError
