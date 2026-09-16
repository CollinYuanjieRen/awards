import Erdos387Proof.SeparatedOuterPartial
import Erdos387Proof.SeparatedZeroDecay

/-! Actual separated almost-prime error counting on the original
squarefree candidate family. The zero mode, the retained nonzero Fourier
remainder and the truncation tail all vanish against the same original
refined sieve scale. -/

set_option autoImplicit false

namespace Erdos387Proof.SeparatedError

open Erdos387 Erdos387.CoverBPZ
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

theorem tendsto_totalPartialRemainder_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => |SeparatedPartialFourier.totalPartialRemainder S N| / sieveScale S N)
      atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (SeparatedTotalEnvelope.tendsto_finiteEnvelope_div_sieveScale_zero S)
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (abs_nonneg _) (sieveScale_pos S N).le
  · filter_upwards [SeparatedOuterPartial.eventually_abs_totalPartialRemainder_le S hB]
      with N hN
    exact div_le_div_of_nonneg_right hN (sieveScale_pos S N).le

theorem tendsto_abs_signedTail_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => |SeparatedFourierTailDecay.signedTail S N| / sieveScale S N)
      atTop (𝓝 0) := by
  have heq : ∀ N : ℕ, |SeparatedFourierTailDecay.signedTail S N| / sieveScale S N =
      |SeparatedFourierTailDecay.signedTail S N / sieveScale S N| := by
    intro N
    rw [abs_div, abs_of_pos (sieveScale_pos S N)]
  simp only [heq]
  simpa using (SeparatedFourierTailDecay.tendsto_signedTail_div_sieveScale_zero S hB).abs

/-- The original squarefree separated almost-prime error count vanishes
relative to the same original sieve density as the candidate lower
bound. -/
theorem tendsto_separated_card_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N =>
      ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedSeparatedAlmostPrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)).card : ℝ) /
      sieveScale S N) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  have hlim := ((SeparatedZeroDecay.tendsto_totalZeroMass_div_sieveScale_zero S hB).add
    (tendsto_totalPartialRemainder_div_sieveScale_zero S hB)).add
    (tendsto_abs_signedTail_div_sieveScale_zero S hB)
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (Nat.cast_nonneg _) (sieveScale_pos S N).le
  · filter_upwards [SubpowerScale.eventually_const_le_z hk (2*S.k)] with N hz
    have h := div_le_div_of_nonneg_right
      (SeparatedPartialFourier.card_separated_le_zero_partial_tail S N hz)
      (sieveScale_pos S N).le
    simpa only [add_div] using h

end Erdos387Proof.SeparatedError
