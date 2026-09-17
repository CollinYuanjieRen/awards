import Mathlib

/-!
# Erdős Problem #265: Cantor's sequence `a_n = C(n, 2)` has both reciprocal sums rational

Erdős asked how fast an increasing sequence of integers `1 ≤ a₁ < a₂ < ⋯` can grow if both
`∑ 1/aₙ` and `∑ 1/(aₙ − 1)` are rational (OPEN in its sharp form; Kovač–Tao proved doubly
exponential growth is possible; not addressed here).  The problem page records: "Cantor observed
that `aₙ = C(n, 2)` is such a sequence."  This file proves that observation: the sequence of
triangular numbers `aₙ = C(n + 3, 2) = 3, 6, 10, 15, …` (Cantor's `C(n, 2)` for `n ≥ 3`, the terms
for which `aₙ − 1 ≥ 1`) is strictly increasing, and both `∑ 1/aₙ` and `∑ 1/(aₙ − 1)` converge to
rational numbers, namely `1` and `11/9`.  No growth statement is claimed.

Proof.  `1/C(n+3, 2) = 2/((n+2)(n+3)) = 2/(n+2) − 2/(n+3)` telescopes to `1`, and
`C(n+3, 2) − 1 = (n+1)(n+4)/2`, so `1/(C(n+3, 2) − 1) = (2/3)(1/(n+1) − 1/(n+4))` telescopes to
`(2/3)(1 + 1/2 + 1/3) = 11/9`.
-/

/-- Closed form for the witness sequence: `2 * C(n+3, 2) = (n+3)(n+2)`. -/
private lemma two_mul_choose_two (n : ℕ) :
    2 * ((n + 3).choose 2) = (n + 3) * (n + 2) := by
  have hd : 2 ∣ (n + 3) * (n + 2) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk
    · exact ⟨(2 * k + 3) * (k + 1), by ring⟩
    · exact ⟨(k + 2) * (2 * k + 3), by ring⟩
  rw [Nat.choose_two_right]
  have h : n + 3 - 1 = n + 2 := by omega
  rw [h]
  exact Nat.mul_div_cancel' hd

/-- Every term of the witness sequence is at least `3`. -/
private lemma three_le_choose_two (n : ℕ) : 3 ≤ (n + 3).choose 2 := by
  have h1 := two_mul_choose_two n
  have h2 : 6 ≤ (n + 3) * (n + 2) := by
    have h := Nat.mul_le_mul (show 3 ≤ n + 3 by omega) (show 2 ≤ n + 2 by omega)
    simpa using h
  omega

/-- The witness sequence is strictly increasing. -/
private lemma strictMono_choose_two : StrictMono (fun n : ℕ ↦ (n + 3).choose 2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := two_mul_choose_two n
  have h2 := two_mul_choose_two (n + 1)
  have h3 : (n + 3) * (n + 2) < (n + 1 + 3) * (n + 1 + 2) := by nlinarith
  show (n + 3).choose 2 < (n + 1 + 3).choose 2
  omega

/-- Real closed form of the witness sequence. -/
private lemma cast_choose_two (n : ℕ) :
    (((n + 3).choose 2 : ℕ) : ℝ) = ((n : ℝ) + 3) * ((n : ℝ) + 2) / 2 := by
  have h : ((2 * ((n + 3).choose 2) : ℕ) : ℝ) = (((n + 3) * (n + 2) : ℕ) : ℝ) := by
    rw [two_mul_choose_two n]
  push_cast at h
  linarith

/-- Telescoping sum with shift `3`. -/
private lemma sum_range_sub_three (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (f i - f (i + 3))
      = f 0 + f 1 + f 2 - f N - f (N + 1) - f (N + 2) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have e1 : k + 1 + 1 = k + 2 := by omega
    have e2 : k + 1 + 2 = k + 3 := by omega
    rw [e1, e2]
    ring

/-- `c / (N + k) → 0` along `N : ℕ → ∞`. -/
private lemma tendsto_div_natCast_add (c k : ℝ) :
    Filter.Tendsto (fun N : ℕ ↦ c / ((N : ℝ) + k)) Filter.atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds
    (Filter.tendsto_atTop_add_const_right Filter.atTop k tendsto_natCast_atTop_atTop)

/-- `∑ 1/C(n+3, 2) = 1`. -/
lemma hasSum_inv_choose_two :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (((n + 3).choose 2 : ℕ) : ℝ)) ((1 : ℚ) : ℝ) := by
  have hnn : ∀ i : ℕ, 0 ≤ (1 : ℝ) / (((i + 3).choose 2 : ℕ) : ℝ) := fun i ↦ by positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn, show ((1 : ℚ) : ℝ) = 1 by norm_num]
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ m : ℕ, g m = 2 / ((m : ℝ) + 2) := ⟨_, fun _ ↦ rfl⟩
  have key : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, (1 : ℝ) / (((i + 3).choose 2 : ℕ) : ℝ))
        = 1 - 2 / ((N : ℝ) + 2) := by
    intro N
    have hterm : ∀ i ∈ Finset.range N,
        (1 : ℝ) / (((i + 3).choose 2 : ℕ) : ℝ) = g i - g (i + 1) := by
      intro i _
      have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
      have h3 : ((i : ℝ) + 3) ≠ 0 := by positivity
      rw [hg, hg, cast_choose_two i]
      push_cast
      rw [div_sub_div _ _ h2 (by positivity : ((i : ℝ) + 1 + 2) ≠ 0)]
      rw [one_div_div]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' g N, hg, hg]
    norm_num
  refine Filter.Tendsto.congr (fun N ↦ (key N).symm) ?_
  simpa using tendsto_const_nhds.sub (tendsto_div_natCast_add 2 2)

/-- `∑ 1/(C(n+3, 2) - 1) = 11/9`. -/
private lemma hasSum_inv_choose_two_sub_one :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / ((((n + 3).choose 2 : ℕ) : ℝ) - 1)) (((11 / 9 : ℚ)) : ℝ) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < (((n + 3).choose 2 : ℕ) : ℝ) - 1 := by
    intro n
    have h : (3 : ℝ) ≤ (((n + 3).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast three_le_choose_two n
    linarith
  have hnn : ∀ i : ℕ, 0 ≤ (1 : ℝ) / ((((i + 3).choose 2 : ℕ) : ℝ) - 1) := fun i ↦
    le_of_lt (div_pos one_pos (hpos i))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn, show ((11 / 9 : ℚ) : ℝ) = 11 / 9 by norm_num]
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ m : ℕ, g m = (2 / 3) / ((m : ℝ) + 1) := ⟨_, fun _ ↦ rfl⟩
  have key : ∀ N : ℕ,
      (∑ i ∈ Finset.range N, (1 : ℝ) / ((((i + 3).choose 2 : ℕ) : ℝ) - 1))
        = 11 / 9 - (2 / 3) / ((N : ℝ) + 1) - (2 / 3) / ((N : ℝ) + 2)
            - (2 / 3) / ((N : ℝ) + 3) := by
    intro N
    have hterm : ∀ i ∈ Finset.range N,
        (1 : ℝ) / ((((i + 3).choose 2 : ℕ) : ℝ) - 1) = g i - g (i + 3) := by
      intro i _
      have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
      have h4 : ((i : ℝ) + 4) ≠ 0 := by positivity
      have hc : (((i + 3 : ℕ) : ℝ) + 1) = (i : ℝ) + 4 := by push_cast; ring
      rw [hg, hg, hc, cast_choose_two i,
        show ((i : ℝ) + 3) * ((i : ℝ) + 2) / 2 - 1 = ((i : ℝ) + 1) * ((i : ℝ) + 4) / 2 by ring,
        one_div_div, div_sub_div _ _ h1 h4,
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [Finset.sum_congr rfl hterm, sum_range_sub_three g N]
    simp only [hg]
    push_cast
    ring_nf
  refine Filter.Tendsto.congr (fun N ↦ (key N).symm) ?_
  have t1 := tendsto_div_natCast_add (2 / 3 : ℝ) 1
  have t2 := tendsto_div_natCast_add (2 / 3 : ℝ) 2
  have t3 := tendsto_div_natCast_add (2 / 3 : ℝ) 3
  simpa using ((tendsto_const_nhds.sub t1).sub t2).sub t3

/-- **Erdős #265, Cantor's observation**: there is an increasing sequence of integers `≥ 2` whose
reciprocal sum and whose "reciprocal minus one" sum are both rational (as genuine convergent
sums). The witness is `a n = (n + 3).choose 2`, i.e. `C(n, 2)` for `n ≥ 3`. -/
theorem erdos_265_cantor :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 2 ≤ a n) ∧
      (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / (a n : ℝ)) (q : ℝ)) ∧
      (∃ q : ℚ, HasSum (fun n ↦ (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) := by
  exact ⟨fun n ↦ (n + 3).choose 2, strictMono_choose_two,
    fun n ↦ le_trans (by norm_num) (three_le_choose_two n),
    ⟨1, hasSum_inv_choose_two⟩, ⟨11 / 9, hasSum_inv_choose_two_sub_one⟩⟩
