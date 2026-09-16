import MerLeanExperiment.Subdivision

open Filter Set
open scoped BigOperators Topology

namespace Erdos492Real

noncomputable section

theorem signedMean_eq_frequency (a : ℕ → ℝ) (α : ℝ) {N : ℕ} (hN : 0 < N) :
    signedMean a α N = 2 * visitFrequency a α (1 / 2) N - 1 := by
  classical
  let A := (Finset.Icc 1 N).filter
    (fun n : ℕ => (n : ℝ) * α ∈ sequenceRegion a (1 / 2))
  have hcard : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        if (n : ℝ) * α ∈ sequenceRegion a (1 / 2) then (1 : ℝ) else -1) =
        2 * A.card - N := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 N,
          (2 * (if (n : ℝ) * α ∈ sequenceRegion a (1 / 2) then (1 : ℝ) else 0) - 1) := by
            apply Finset.sum_congr rfl
            intro n hn
            split <;> norm_num
      _ = 2 * A.card - N := by
        rw [Finset.sum_sub_distrib]
        congr 1
        · rw [← Finset.mul_sum]
          simp [A]
        · simp [hcard]
  rw [signedMean, visitFrequency, hsum]
  change (2 * (A.card : ℝ) - N) / N =
    2 * ((A.card : ℝ) / N) - 1
  field_simp

theorem UniformlyDistributed.tendsto_signedMean {a : ℕ → ℝ} {α : ℝ}
    (h : UniformlyDistributed a α) :
    Tendsto (signedMean a α) atTop (𝓝 0) := by
  have hfreq := h (1 / 2) (by norm_num) (by norm_num)
  have heq : ∀ᶠ N in atTop,
      signedMean a α N = 2 * visitFrequency a α (1 / 2) N - 1 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    exact signedMean_eq_frequency a α (by omega)
  have ht : Tendsto (fun N => 2 * visitFrequency a α (1 / 2) N - 1)
      atTop (𝓝 0) := by
    (convert (hfreq.const_mul 2).sub tendsto_const_nhds using 1; norm_num)
  apply Tendsto.congr' _ ht
  filter_upwards [heq] with N hN
  exact hN.symm

theorem not_tendsto_zero_of_large_subsequence {f : ℕ → ℝ}
    (hlarge : ∀ ε : ℝ, 0 < ε → ∀ B : ℕ,
      ∃ N : ℕ, B ≤ N ∧ |f N| > 1 - ε) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro hf
  have hevent : ∀ᶠ N in atTop, |f N| < (1 / 2 : ℝ) := by
    have habs : Tendsto (fun N => |f N|) atTop (𝓝 |(0 : ℝ)|) :=
      (continuous_abs.tendsto 0).comp hf
    simpa only [abs_zero] using
      (tendsto_order.1 habs).2 (1 / 2) (by norm_num)
  obtain ⟨B, hB⟩ := eventually_atTop.1 hevent
  obtain ⟨N, hBN, hN⟩ := hlarge (1 / 2) (by norm_num) B
  have := hB N hBN
  norm_num at hN
  linarith

theorem not_uniformlyDistributed_of_large_signedMean {a : ℕ → ℝ} {α : ℝ}
    (hlarge : ∀ ε : ℝ, 0 < ε → ∀ B : ℕ,
      ∃ N : ℕ, B ≤ N ∧ |signedMean a α N| > 1 - ε) :
    ¬ UniformlyDistributed a α := by
  intro h
  exact not_tendsto_zero_of_large_subsequence hlarge h.tendsto_signedMean

end

end Erdos492Real
