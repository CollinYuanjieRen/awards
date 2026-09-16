/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Erdos387Proof.ExistingCountingBounds
import Erdos387Proof.MediumError
import Erdos387Proof.SquarefreeErrorExhaustion

/-!
# Conditional main assembly for Erdős problem 387

This file combines the five refined error counts on the subpower scale into the
negative answer to Erdős 387, *conditionally* on the two error limits (E3
convenient, E5 separated) that are supplied here as explicit hypotheses.

The three remaining ingredients are unconditional:

* `ExistingCountingBounds.tendsto_squarefree_large_div_sieveScale_zero` (E1),
* `MediumError.tendsto_medium_card_div_sieveScale_zero` (E2),
* the comparable-prime budget produced by
  `ExistingCountingBounds.exists_cover_with_comparable_budget` (E4),

together with the squarefree candidate lower bound
`ExistingCountingBounds.eventually_squarefree_card_ge`, the finite five-error
cover `SquarefreeErrorExhaustion.bad_squarefree_card_le_five` and the extraction
`SquarefreeErrorExhaustion.exists_counterexample_of_bad_squarefree_card_lt`.

Fully proved; the axiom footprint is the Lean/Mathlib standard triple
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace Erdos387Proof.MainAssembly

open Erdos387 Erdos387.CoverBPZ Filter
open ExistingCountingBounds SquarefreeErrorExhaustion MediumSubpowerReduction
open scoped Topology

/-- The negative answer to Erdős 387, conditional on the convenient (E3) and
separated almost-prime (E5) error limits. -/
theorem main_of_limits
    (hE3 : ∀ {B K : ℕ} (S : BPZSection6Input B K), 0 < B →
      Tendsto (fun N => ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedConvenientErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)).card : ℝ) / sieveScale S N) atTop (𝓝 0))
    (hE5 : ∀ {B K : ℕ} (S : BPZSection6Input B K), 0 < B →
      Tendsto (fun N => ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedSeparatedAlmostPrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)).card : ℝ) / sieveScale S N) atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  classical
  rintro ⟨c, hc, hdiv⟩
  -- 1. choose `B ≥ 3` with `1/B ≤ c`.
  obtain ⟨B, hB3, hBc⟩ : ∃ B : ℕ, 3 ≤ B ∧ (1 : ℝ) / B ≤ c := by
    refine ⟨max 3 ⌈1 / c⌉₊, le_max_left _ _, ?_⟩
    have hpos : (0 : ℝ) < 1 / c := by positivity
    have h1 : (1 : ℝ) / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / c⌉₊ : ℕ) : ℝ) ≤ ((max 3 ⌈1 / c⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right 3 ⌈1 / c⌉₊
    have h3 := one_div_le_one_div_of_le hpos (h1.trans h2)
    rwa [one_div_one_div] at h3
  have hB : 0 < B := by omega
  -- 2. cover with an E4 (comparable-prime) budget `δ = 1/128`.
  obtain ⟨S, hcomp⟩ := exists_cover_with_comparable_budget B 0 hB3 (1 / 128) (by norm_num)
  have hk3 : 3 ≤ S.k := S.hk3
  -- 3. the four vanishing normalized error counts.
  have hE1 := tendsto_squarefree_large_div_sieveScale_zero S hB
  have hE2 := MediumError.tendsto_medium_card_div_sieveScale_zero S hB
  have hE3' := hE3 S hB
  have hE5' := hE5 S hB
  have hlt : ∀ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) → ∀ᶠ N : ℕ in atTop, f N < 1 / 256 :=
    fun f hf => hf.eventually (gt_mem_nhds (by norm_num))
  -- 4. squarefree lower bound and the finite scale side condition.
  have hlowE := eventually_squarefree_card_ge S
  have hbaseE := MediumFourierTailDecay.eventually_const_le_base S.k (2 * B)
  -- 5. every large enough `N` yields a contradiction.
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hlowE, hcomp, hlt _ hE1, hlt _ hE2, hlt _ hE3', hlt _ hE5', hbaseE]
      with N hlow hcomp h1 h2 h3 h5 hbase
    have hss : (0 : ℝ) < sieveScale S N := sieveScale_pos S N
    have hbase2 : 2 ≤ SubpowerScale.base N S.k := by omega
    have hbase0 : 0 < SubpowerScale.base N S.k := by omega
    -- scale side conditions for the five-error cover
    have hy2 : 2 ≤ SubpowerScale.y N S.k := by
      have hyE : BPZScale.yExp S.k ≠ 0 := by unfold BPZScale.yExp; positivity
      have hle : SubpowerScale.base N S.k ≤ SubpowerScale.y N S.k := by
        simpa [SubpowerScale.y, BPZScale.y] using
          Nat.le_self_pow hyE (SubpowerScale.base N S.k)
      omega
    have hsecond : 1 ≤ SubpowerScale.secondMin N S.k := by
      simpa [SubpowerScale.secondMin, BPZScale.secondMin] using
        Nat.one_le_pow (BPZScale.secondExp S.k) (SubpowerScale.base N S.k) hbase0
    have hscaleSecond := SubpowerScale.almostSecond_scale (B := B) hk3 hbase
    have hscaleGap := SubpowerScale.almostGap_scale (B := B) hk3 hbase
    have hfive := bad_squarefree_card_le_five (X := SubpowerScale.X N S.k)
      (z := SubpowerScale.z N S.k) (y := SubpowerScale.y N S.k)
      (medium := SubpowerScale.medium N S.k) (large := SubpowerScale.large N S.k)
      (secondMin := SubpowerScale.secondMin N S.k) (gap := SubpowerScale.gap N S.k)
      S hB hy2 hsecond hscaleSecond hscaleGap
    -- the E4 budget, restricted to the squarefree candidates
    have hc4 : ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedComparablePrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
          (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)
          (SubpowerScale.medium N S.k)).card : ℝ) / sieveScale S N < 1 / 128 := by
      refine lt_of_le_of_lt ?_ hcomp
      apply div_le_div_of_nonneg_right _ (sieveScale_pos S N).le
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have key : ∀ (m : ℕ) (r : ℝ), (m : ℝ) / sieveScale S N < r →
        (m : ℝ) < r * sieveScale S N := fun m r h => (div_lt_iff₀ hss).mp h
    have k1 := key _ _ h1
    have k2 := key _ _ h2
    have k3 := key _ _ h3
    have k5 := key _ _ h5
    have k4 := key _ _ hc4
    have hfR : ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedBadCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)).card : ℝ) ≤
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
          RefinedLargeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.large N S.k)).card : ℝ) +
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
          RefinedMediumErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.medium N S.k) (SubpowerScale.large N S.k)).card : ℝ) +
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
          RefinedConvenientErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)).card : ℝ) +
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
          RefinedComparablePrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)
            (SubpowerScale.medium N S.k)).card : ℝ) +
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
          RefinedSeparatedAlmostPrimeErrors S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)
            (SubpowerScale.y N S.k) (SubpowerScale.medium N S.k)
            (SubpowerScale.secondMin N S.k) (SubpowerScale.gap N S.k)).card : ℝ) := by
      exact_mod_cast hfive
    have hsum : ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedBadCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)).card : ℝ) <
        ((RefinedSquarefreeCandidates S (SubpowerScale.X N S.k)
          (SubpowerScale.z N S.k)).card : ℝ) := by
      linarith
    have hcard : (RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k) ∩
        RefinedBadCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)).card <
        (RefinedSquarefreeCandidates S (SubpowerScale.X N S.k) (SubpowerScale.z N S.k)).card := by
      exact_mod_cast hsum
    obtain ⟨n, -, hkn, -, -, hnodiv⟩ :=
      exists_counterexample_of_bad_squarefree_card_lt S hB hcard
    obtain ⟨d, hd, hdvd⟩ := hdiv n S.k (by omega) hkn
    refine hnodiv d ⟨?_, hd.2⟩ hdvd
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hrw : (n : ℝ) / B = (1 / (B : ℝ)) * n := by ring
    rw [hrw]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hBc hn0) hd.1
  obtain ⟨N, hN⟩ := hfalse.exists
  exact hN

end Erdos387Proof.MainAssembly
