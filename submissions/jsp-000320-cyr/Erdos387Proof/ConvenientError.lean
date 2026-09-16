import Erdos387Proof.ConvenientOuterPartial
import Erdos387Proof.ConvenientZeroDecay

/-! Actual convenient-range error counting on the original squarefree
candidate family.  The zero mode, the retained nonzero Fourier remainder and
the truncation tail all vanish against the same original refined sieve
scale. -/

set_option autoImplicit false

namespace Erdos387Proof.ConvenientError

open Erdos387 Erdos387.CoverBPZ
open MediumFourierTailDecay MediumSubpowerReduction Filter
open scoped BigOperators Topology

theorem tendsto_totalPartialRemainder_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => |ConvenientPartialFourier.totalPartialRemainder S N| / sieveScale S N)
      atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · exact Filter.Eventually.of_forall fun N =>
      hc.trans_le (div_nonneg (abs_nonneg _) (sieveScale_pos S N).le)
  · exact ConvenientOuterPartial.eventually_abs_totalPartialRemainder_div_sieveScale_lt
      S hB hc

theorem tendsto_abs_signedTail_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => |ConvenientFourierTailDecay.signedTail S N| / sieveScale S N)
      atTop (𝓝 0) := by
  have heq : ∀ N : ℕ, |ConvenientFourierTailDecay.signedTail S N| / sieveScale S N =
      |ConvenientFourierTailDecay.signedTail S N / sieveScale S N| := by
    intro N
    rw [abs_div, abs_of_pos (sieveScale_pos S N)]
  simp only [heq]
  simpa using
    (ConvenientFourierTailDecay.tendsto_signedTail_div_sieveScale_zero S hB).abs

/-- The original squarefree convenient-range error count vanishes relative
to the same original sieve density as the candidate lower bound. -/
theorem tendsto_convenient_card_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N =>
      ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedConvenientErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)).card : ℝ) /
      sieveScale S N) atTop (𝓝 0) := by
  have hk : 0 < S.k := by have := S.hk3; omega
  have hlim := ((ConvenientZeroDecay.tendsto_totalZeroMass_div_sieveScale_zero S hB).add
    (tendsto_totalPartialRemainder_div_sieveScale_zero S hB)).add
    (tendsto_abs_signedTail_div_sieveScale_zero S hB)
  simp only [add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (Nat.cast_nonneg _) (sieveScale_pos S N).le
  · filter_upwards [SubpowerScale.eventually_const_le_z hk (2*S.k)] with N hz
    have h := div_le_div_of_nonneg_right
      (ConvenientPartialFourier.card_convenient_le_zero_partial_tail S N hz)
      (sieveScale_pos S N).le
    simpa only [add_div] using h

end Erdos387Proof.ConvenientError
