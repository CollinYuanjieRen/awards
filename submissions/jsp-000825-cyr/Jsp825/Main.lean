import Jsp825.Blocks
import Jsp825.Growth
import Jsp825.Digits

/-!
# JSP-000825 / Erdős #992 — the three roots

Assembling the pieces: the discrepancy of the constructed sequence `x` is `≥ (1/64)√(N log N)`
infinitely often for almost every `α ∈ [0,1]`, which answers both questions of the problem
in the negative.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-! ### The discrepancy dominates the error of a single interval -/

/-- At most `N` of the first `N` points lie in `I`. -/
theorem count_le (x : ℕ → ℤ) (α : ℝ) (n : ℕ) (I : Set ℝ) : count x α n I ≤ n := by
  classical
  unfold count
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (le_of_eq ?_)
  exact Finset.card_range n

/-- A sub-interval of `[0,1]` has length at most `1`. -/
theorem volume_toReal_le_one {I : Set ℝ} (hI : I ⊆ Icc (0 : ℝ) 1) : (volume I).toReal ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  refine le_trans (measure_mono hI) ?_
  rw [Real.volume_Icc]
  norm_num

/-- Every single-interval error is bounded by `N`. -/
theorem abs_err_le (x : ℕ → ℤ) (α : ℝ) (n : ℕ) {I : Set ℝ} (hI : I ⊆ Icc (0 : ℝ) 1) :
    |err x α n I| ≤ n := by
  have hcount : (count x α n I : ℝ) ≤ (n : ℝ) := by exact_mod_cast count_le x α n I
  have hcount0 : (0 : ℝ) ≤ (count x α n I : ℝ) := Nat.cast_nonneg _
  have hvol1 : (volume I).toReal ≤ 1 := volume_toReal_le_one hI
  have hvol0 : (0 : ℝ) ≤ (volume I).toReal := ENNReal.toReal_nonneg
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have h1 : (volume I).toReal * (n : ℝ) ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hvol1 hn0
  have h2 : (0 : ℝ) ≤ (volume I).toReal * (n : ℝ) := mul_nonneg hvol0 hn0
  rw [abs_le]
  unfold err
  constructor <;> linarith only [hcount, hcount0, h1, h2]

/-- The family of single-interval errors is bounded above, so its supremum is meaningful. -/
theorem bddAbove_err (x : ℕ → ℤ) (α : ℝ) (n : ℕ) :
    BddAbove (Set.range fun I : SubInterval ↦ |err x α n I.1|) := by
  refine ⟨(n : ℝ), ?_⟩
  rintro y ⟨I, rfl⟩
  exact abs_err_le x α n I.2.1

/-- The discrepancy dominates the error of each sub-interval. -/
theorem D_ge (x : ℕ → ℤ) (α : ℝ) (n : ℕ) (I : SubInterval) : |err x α n I.1| ≤ D x α n :=
  le_csSup (bddAbove_err x α n) ⟨I, rfl⟩

/-- `I₀ = [0, 1/2)` is a sub-interval of `[0,1]`. -/
theorem I₀_mem : I₀ ⊆ Icc (0 : ℝ) 1 ∧ I₀.OrdConnected := by
  constructor
  · rw [I₀]
    intro y hy
    rw [mem_Ico] at hy
    exact ⟨hy.1, by linarith only [hy.2]⟩
  · rw [I₀]
    exact ordConnected_Ico

/-- The discrepancy dominates the error of the witness interval `I₀`. -/
theorem abs_err_I₀_le_D (x : ℕ → ℤ) (α : ℝ) (n : ℕ) : |err x α n I₀| ≤ D x α n :=
  D_ge x α n ⟨I₀, I₀_mem⟩

/-! ### The two-`N` trick -/

/-- If `α` realises the digit event of block `j ≥ 4`, then at one of the two endpoints
`N (j-1)`, `N j` of the block the discrepancy is at least `(1/64) √(n log n)`. -/
theorem exists_large_D {j : ℕ} {α : ℝ} (hj : 4 ≤ j) (hE : α ∈ E j) :
    ∃ n : ℕ, N (j - 1) ≤ n ∧ (1 / 64 : ℝ) * Real.sqrt (n * Real.log n) ≤ D x α n := by
  have hβ := fract_mem_of_mem_E hE
  have hstep := err_block j α hj hβ
  have hD1 := abs_err_I₀_le_D x α (N j)
  have hD2 := abs_err_I₀_le_D x α (N (j - 1))
  have ha1 := le_abs_self (err x α (N j) I₀)
  have ha2 := neg_abs_le (err x α (N (j - 1)) I₀)
  have hsum : (L j : ℝ) / 8 ≤ D x α (N j) + D x α (N (j - 1)) := by
    linarith only [hstep, hD1, hD2, ha1, ha2]
  have hle : N (j - 1) ≤ N j := N_mono.monotone (Nat.sub_le j 1)
  by_cases hcase : (L j : ℝ) / 16 ≤ D x α (N j)
  · refine ⟨N j, hle, ?_⟩
    have hsq := sqrt_NlogN_le_of_le (j := j) (n := N j) (by omega) le_rfl
    linarith only [hsq, hcase]
  · refine ⟨N (j - 1), le_rfl, ?_⟩
    have hlt := not_le.1 hcase
    have hsq := sqrt_NlogN_le_of_le (j := j) (n := N (j - 1)) (by omega) hle
    linarith only [hsq, hsum, hlt]

/-! ### Almost sure lower bound for the constructed sequence -/

/-- **The Berkes–Philipp bound for the constructed sequence `x`.** -/
theorem bp_x : ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
    ∃ᶠ n : ℕ in atTop, (1 / 64 : ℝ) * Real.sqrt (n * Real.log n) ≤ D x α n := by
  have hdiv := prod_tendsto_zero p_ge p_le_one p_nonneg
  filter_upwards [ae_frequently_E hdiv] with α hα hα01
  have hfreq := hα hα01
  rw [Filter.frequently_atTop]
  intro n₀
  obtain ⟨j₁, hj₁⟩ := (tendsto_atTop_atTop.1 N_tendsto) n₀
  obtain ⟨j, hjge, hjE⟩ := Filter.frequently_atTop.1 hfreq (max 4 (j₁ + 1))
  have h4 : 4 ≤ j := le_trans (le_max_left _ _) hjge
  have hj1 : j₁ ≤ j - 1 := by
    have h := le_trans (le_max_right 4 (j₁ + 1)) hjge
    omega
  obtain ⟨n, hn1, hn2⟩ := exists_large_D h4 hjE
  exact ⟨n, le_trans (hj₁ (j - 1) hj1) hn1, hn2⟩

/-- **Berkes–Philipp**: a sequence whose discrepancy is `≫ (N log N)^{1/2}` infinitely often,
for almost all `α ∈ [0,1]`. -/
theorem berkes_philipp :
    ∃ x : ℕ → ℤ, StrictMono x ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᵐ α ∂volume, α ∈ Icc (0 : ℝ) 1 →
        ∃ᶠ N : ℕ in atTop, c * Real.sqrt (N * Real.log N) ≤ D x α N :=
  ⟨x, x_strictMono, 1 / 64, by norm_num, bp_x⟩

/-! ### The two questions -/

/-- An almost-everywhere property holds at some point of `[0,1]`, since `[0,1]` is not null. -/
theorem exists_mem_Icc_of_ae {P : ℝ → Prop} (h : ∀ᵐ α ∂volume, P α) :
    ∃ α ∈ Icc (0 : ℝ) 1, P α := by
  have hμ : volume.restrict (Icc (0 : ℝ) 1) ≠ 0 := by
    intro hzero
    have h0 : (volume.restrict (Icc (0 : ℝ) 1)) univ = 0 := by rw [hzero]; simp
    rw [Measure.restrict_apply_univ, Real.volume_Icc] at h0
    simp at h0
  have hne : NeBot (ae (volume.restrict (Icc (0 : ℝ) 1))) := ae_neBot.2 hμ
  have h1 : ∀ᵐ α ∂(volume.restrict (Icc (0 : ℝ) 1)), P α ∧ α ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_of_ae h).and (ae_restrict_mem measurableSet_Icc)
  obtain ⟨α, hP, hmem⟩ := h1.exists
  exact ⟨α, hmem, hP⟩

/-- The first question has the answer no. -/
theorem not_erdos_992 : ¬ Erdos992Statement := by
  intro h
  obtain ⟨α, hα01, hA, hB⟩ := exists_mem_Icc_of_ae ((h x x_strictMono).and bp_x)
  obtain ⟨C, hC⟩ := hA hα01 (1 / 4) (by norm_num)
  have hfreq := hB hα01
  have hlt := eventually_log_pow_lt (1 / 4) C (by norm_num)
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hC.and hlt)).exists
  linarith only [hn1, hn2, hn3]

/-- The "or even" question has the answer no. -/
theorem not_erdos_992_loglog : ¬ Erdos992StatementLogLog := by
  intro h
  obtain ⟨α, hα01, hA, hB⟩ := exists_mem_Icc_of_ae ((h x x_strictMono).and bp_x)
  obtain ⟨C, K, hC⟩ := hA hα01
  have hfreq := hB hα01
  have hlt := eventually_loglog_pow_lt K C
  obtain ⟨n, hn1, hn2, hn3⟩ := (hfreq.and_eventually (hC.and hlt)).exists
  linarith only [hn1, hn2, hn3]

end Erdos992
