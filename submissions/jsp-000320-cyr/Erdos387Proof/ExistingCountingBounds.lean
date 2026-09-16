import ErdosProblems.Erdos387.SubpowerSquarefree
import ErdosProblems.Erdos387.SubpowerComparable
import ErdosProblems.Erdos387.UnconditionalCover
import Erdos387Proof.MediumSubpowerReduction

/-! Previously established counts at the common original sieve scale.
The comparable-prime budget is obtained by choosing the cover parameter;
it is not an additional premise on the final counterexample. -/

set_option autoImplicit false

namespace Erdos387Proof.ExistingCountingBounds

open Erdos387 Erdos387.CoverBPZ MediumMainTermDecay MediumSubpowerReduction Filter
open scoped Topology

theorem eventually_squarefree_card_ge {B K : ℕ} (S : BPZSection6Input B K) :
    ∀ᶠ N : ℕ in atTop, sieveScale S N / 32 ≤
      ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k)).card : ℝ) := by
  convert SubpowerScale.eventually_refinedSquarefreeCandidates_card_ge_scale S using 1
  simp only [sieveScale, refinedDensity, div_div, mul_comm]

theorem tendsto_large_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => ((RefinedLargeErrors S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.large N S.k)).card : ℝ) /
        sieveScale S N) atTop (𝓝 0) := by
  have h := (SubpowerScale.tendsto_refinedLargeErrors_normalized_zero S hB).mul_const
    (refinementModulus S : ℝ)
  simpa only [sieveScale, refinedDensity, div_div_eq_mul_div, div_mul_eq_mul_div,
    zero_mul] using h

theorem eventually_comparable_div_sieveScale_lt {B K : ℕ}
    (S : BPZSection6Input B K) (C : ℝ) (hC : 0 < C)
    (hcheb : ∀ t : ℕ, 2 ≤ t → (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (δ : ℝ) (hδ : 0 < δ)
    (hk : 36 * (2 * C / Real.log 2)^2 < δ * S.k) :
    ∀ᶠ N : ℕ in atTop,
      ((RefinedComparablePrimeErrors S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.secondMin N S.k)
        (SubpowerScale.gap N S.k) (SubpowerScale.medium N S.k)).card : ℝ) /
          sieveScale S N < δ := by
  have hM : (0 : ℝ) < refinementModulus S := by exact_mod_cast refinementModulus_pos S
  have hkpos : (0 : ℝ) < S.k := by exact_mod_cast (show 0 < S.k by have := S.hk3; omega)
  have heps : 0 < δ / (2 * refinementModulus S : ℝ) := by positivity
  filter_upwards [SubpowerScale.eventually_refinedComparablePrimeErrors_normalized_lt
    S C hC hcheb _ heps] with N hN
  have hb : 18 * (2 * C / Real.log 2)^2 / (S.k : ℝ) < δ / 2 := by
    apply (div_lt_iff₀ hkpos).mpr
    nlinarith
  have ht := mul_lt_mul_of_pos_right hN hM
  have heq : (18 * (2 * C / Real.log 2)^2 /
      ((refinementModulus S : ℝ) * S.k) + δ / (2 * refinementModulus S)) *
        refinementModulus S = 18 * (2 * C / Real.log 2)^2 / S.k + δ / 2 := by
    field_simp
  rw [heq] at ht
  have heq' : ((RefinedComparablePrimeErrors S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.secondMin N S.k)
      (SubpowerScale.gap N S.k) (SubpowerScale.medium N S.k)).card : ℝ) /
        sieveScale S N =
      ((RefinedComparablePrimeErrors S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.secondMin N S.k)
      (SubpowerScale.gap N S.k) (SubpowerScale.medium N S.k)).card : ℝ) /
        ((SubpowerScale.X N S.k : ℝ) * refinedDensity S (SubpowerScale.z N S.k)) *
          refinementModulus S := by
    unfold sieveScale
    rw [div_div_eq_mul_div]
    ring
  rw [heq']
  change _ < _ at ht
  exact ht.trans (by linarith)

theorem tendsto_squarefree_large_div_sieveScale_zero {B K : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) :
    Tendsto (fun N => ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) ∩ RefinedLargeErrors S (SubpowerScale.X N S.k)
      (SubpowerScale.z N S.k) (SubpowerScale.large N S.k)).card : ℝ) /
        sieveScale S N) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_large_div_sieveScale_zero S hB)
  · exact Filter.Eventually.of_forall (fun N =>
      div_nonneg (Nat.cast_nonneg _) (sieveScale_pos S N).le)
  · apply Filter.Eventually.of_forall
    intro N
    apply div_le_div_of_nonneg_right _ (sieveScale_pos S N).le
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right

theorem exists_cover_with_comparable_budget (B K : ℕ) (hB : 3 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : BPZSection6Input B K, ∀ᶠ N : ℕ in atTop,
      ((RefinedComparablePrimeErrors S (SubpowerScale.X N S.k)
        (SubpowerScale.z N S.k) (SubpowerScale.secondMin N S.k)
        (SubpowerScale.gap N S.k) (SubpowerScale.medium N S.k)).card : ℝ) /
          sieveScale S N < δ := by
  obtain ⟨C, hC, hcheb⟩ := PrimeReciprocal.exists_uniform_primeCounting_le_div_log_all
  obtain ⟨J, hJ⟩ := exists_nat_gt (36 * (2 * C / Real.log 2)^2 / δ)
  obtain ⟨T, _⟩ := unconditional_fixed_B_cover_section6_input B (max K J) hB
  let S : BPZSection6Input B K := { T with hkK := (le_max_left K J).trans T.hkK }
  refine ⟨S, eventually_comparable_div_sieveScale_lt S C hC hcheb δ hδ ?_⟩
  have hJk : (J : ℝ) ≤ S.k := by
    exact_mod_cast (le_max_right K J).trans T.hkK
  have hlt := (div_lt_iff₀ hδ).mp (hJ.trans_le hJk)
  simpa [mul_comm] using hlt

end Erdos387Proof.ExistingCountingBounds
