import Jsp825.Params

/-!
# Growth estimates for the construction

Prefix bounds `N j ≤ (i+1) 4^(i+1)` (`i = grp j`), the resulting `√(N log N) ≤ 4 L j`,
divergence of `∑ p j` and the two "eventually" comparisons used in the assembly.
-/

open MeasureTheory Filter Set

namespace Erdos992

/-! ### Basic facts about `grp` and `L` -/

theorem two_pow_grp_le {j : ℕ} (hj : 1 ≤ j) : 2 ^ grp j ≤ j :=
  Nat.pow_log_le_self 2 (by omega)

theorem lt_two_pow_grp (j : ℕ) : j < 2 ^ (grp j + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) j

theorem grp_mono : Monotone grp := fun _ _ h => Nat.log_mono_right h

theorem L_eq (j : ℕ) : L j = (grp j + 1) * 2 ^ grp j := rfl

/-- Crude prefix bound: `N j ≤ (grp j + 1) * j^2`. -/
theorem N_le_sq (j : ℕ) : N j ≤ (grp j + 1) * j ^ 2 := by
  induction j with
  | zero => simp [N]
  | succ k ih =>
      have hmono : grp k ≤ grp (k + 1) := grp_mono (Nat.le_succ k)
      have h1 : N k ≤ (grp (k + 1) + 1) * k ^ 2 :=
        ih.trans (Nat.mul_le_mul_right _ (by omega))
      have h2 : L (k + 1) ≤ (grp (k + 1) + 1) * (k + 1) := by
        rw [L_eq]
        exact Nat.mul_le_mul_left _ (two_pow_grp_le (by omega))
      have h3 : (grp (k + 1) + 1) * k ^ 2 + (grp (k + 1) + 1) * (k + 1)
          ≤ (grp (k + 1) + 1) * (k + 1) ^ 2 := by
        rw [← Nat.mul_add]
        exact Nat.mul_le_mul_left _ (by nlinarith)
      rw [N_succ]
      omega

/-- Prefix bound in terms of the group index. -/
theorem N_le (j : ℕ) : N j ≤ (grp j + 1) * 4 ^ (grp j + 1) := by
  have h1 : j ^ 2 ≤ 4 ^ (grp j + 1) := by
    have := lt_two_pow_grp j
    have : j ^ 2 < (2 ^ (grp j + 1)) ^ 2 := by
      exact Nat.pow_lt_pow_left this (by norm_num)
    calc j ^ 2 ≤ (2 ^ (grp j + 1)) ^ 2 := by omega
      _ = 4 ^ (grp j + 1) := by
          rw [← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul]
  exact (N_le_sq j).trans (Nat.mul_le_mul_left _ h1)

/-! ### `√(n log n) ≤ 4 L j` for `n ≤ N j` -/

theorem log_four_lt : Real.log 4 < 1.4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have h2 := Real.log_two_lt_d9
  rw [h]; linarith only [h2]

theorem cast_N_le (j : ℕ) : (N j : ℝ) ≤ ((grp j : ℝ) + 1) * 4 ^ (grp j + 1) := by
  have h : ((N j : ℕ) : ℝ) ≤ (((grp j + 1) * 4 ^ (grp j + 1) : ℕ) : ℝ) := by
    exact_mod_cast N_le j
  push_cast at h
  linarith only [h]

theorem log_le_of_le_N {j n : ℕ} (hn : n ≤ N j) : Real.log n ≤ 3 * ((grp j : ℝ) + 1) := by
  have hi : (0:ℝ) ≤ (grp j : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.cast_zero, Real.log_zero]
    positivity
  · have hA : (n : ℝ) ≤ ((grp j : ℝ) + 1) * 4 ^ (grp j + 1) := by
      have h : ((n : ℕ) : ℝ) ≤ ((N j : ℕ) : ℝ) := by exact_mod_cast hn
      linarith only [h, cast_N_le j]
    have hlog : Real.log n ≤ Real.log (((grp j : ℝ) + 1) * 4 ^ (grp j + 1)) := by
      refine Real.log_le_log ?_ hA
      exact_mod_cast hpos
    have hsplit : Real.log (((grp j : ℝ) + 1) * 4 ^ (grp j + 1))
        = Real.log ((grp j : ℝ) + 1) + ((grp j : ℝ) + 1) * Real.log 4 := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast; ring
    have h1 : Real.log ((grp j : ℝ) + 1) ≤ (grp j : ℝ) := by
      have := Real.log_le_sub_one_of_pos (x := (grp j : ℝ) + 1) (by positivity)
      linarith only [this]
    have h3 : ((grp j : ℝ) + 1) * Real.log 4 ≤ ((grp j : ℝ) + 1) * 1.4 :=
      mul_le_mul_of_nonneg_left log_four_lt.le (by positivity)
    rw [hsplit] at hlog
    linarith only [hlog, h1, h3, hi]

theorem nlogn_le {j n : ℕ} (hn : n ≤ N j) : (n : ℝ) * Real.log n ≤ (4 * (L j : ℝ)) ^ 2 := by
  have hi : (0:ℝ) ≤ (grp j : ℝ) := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlog : Real.log n ≤ 3 * ((grp j : ℝ) + 1) := log_le_of_le_N hn
  have hA : (n : ℝ) ≤ ((grp j : ℝ) + 1) * 4 ^ (grp j + 1) := by
    have h : ((n : ℕ) : ℝ) ≤ ((N j : ℕ) : ℝ) := by exact_mod_cast hn
    linarith only [h, cast_N_le j]
  have e1 : (4:ℝ) ^ (grp j + 1) = 4 * 4 ^ grp j := by rw [pow_succ]; ring
  have e2 : ((L j : ℕ) : ℝ) = ((grp j : ℝ) + 1) * 2 ^ grp j := by
    rw [L_eq]; push_cast; ring
  have e3 : ((2:ℝ) ^ grp j) ^ 2 = 4 ^ grp j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hX : (0:ℝ) < 4 ^ grp j := by positivity
  have hstep : (n : ℝ) * Real.log n
      ≤ (((grp j : ℝ) + 1) * 4 ^ (grp j + 1)) * (3 * ((grp j : ℝ) + 1)) :=
    mul_le_mul hA hlog hlog0 (by positivity)
  have hrhs : (4 * (L j : ℝ)) ^ 2 = 16 * (((grp j : ℝ) + 1) ^ 2 * 4 ^ grp j) := by
    rw [e2, ← e3]; ring
  have hlhs : (((grp j : ℝ) + 1) * 4 ^ (grp j + 1)) * (3 * ((grp j : ℝ) + 1))
      = 12 * (((grp j : ℝ) + 1) ^ 2 * 4 ^ grp j) := by
    rw [e1]; ring
  have hfin : 12 * (((grp j : ℝ) + 1) ^ 2 * 4 ^ grp j)
      ≤ 16 * (((grp j : ℝ) + 1) ^ 2 * 4 ^ grp j) := by
    have : (0:ℝ) ≤ ((grp j : ℝ) + 1) ^ 2 * 4 ^ grp j := by positivity
    linarith only [this]
  rw [hrhs]
  linarith only [hstep, hlhs, hfin]

/-- Monotone form: for every `n ≤ N j`, `√(n log n) ≤ 4 L j`. -/
theorem sqrt_NlogN_le_of_le {j n : ℕ} (_hj : 1 ≤ j) (hn : n ≤ N j) :
    Real.sqrt (n * Real.log n) ≤ 4 * L j := by
  have h := nlogn_le (j := j) hn
  calc Real.sqrt ((n : ℝ) * Real.log n) ≤ Real.sqrt ((4 * (L j : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = 4 * (L j : ℝ) := Real.sqrt_sq (by positivity)

/-- The growth bound: `√(N j log (N j)) ≤ 4 L j`. -/
theorem sqrt_NlogN_le (j : ℕ) (hj : 1 ≤ j) :
    Real.sqrt (N j * Real.log (N j)) ≤ 4 * L j :=
  sqrt_NlogN_le_of_le hj le_rfl

/-! ### Harmonic divergence of the block probabilities -/

theorem grp_eq_of_mem {i j : ℕ} (h1 : 2 ^ i ≤ j) (h2 : j < 2 ^ (i + 1)) : grp j = i :=
  Nat.log_eq_of_pow_le_of_lt_pow h1 h2

/-- The blocks of group `i` contribute exactly `1 / (8 (i+1))` to `∑ 1 / (8 L j)`. -/
theorem group_sum (i : ℕ) :
    ∑ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)), (1 / (8 * (L j : ℝ)))
      = 1 / (8 * ((i : ℝ) + 1)) := by
  have hcongr : ∀ j ∈ Finset.Ico (2 ^ i) (2 ^ (i + 1)),
      (1 / (8 * (L j : ℝ))) = 1 / (8 * ((i : ℝ) + 1) * 2 ^ i) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have hgrp : grp j = i := grp_eq_of_mem hj.1 hj.2
    rw [L_eq, hgrp]
    push_cast
    ring
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Nat.card_Ico,
    show 2 ^ (i + 1) - 2 ^ i = 2 ^ i by rw [pow_succ]; omega, nsmul_eq_mul]
  have h2 : (0:ℝ) < 2 ^ i := by positivity
  have hi : (0:ℝ) < (i : ℝ) + 1 := by positivity
  push_cast
  field_simp

/-- Summing the group sums: over the blocks `j ∈ [2^I₀, 2^(I+1))`. -/
theorem block_sum (I₀ I : ℕ) (hI₀ : I₀ ≤ I) :
    ∑ j ∈ Finset.Ico (2 ^ I₀) (2 ^ (I + 1)), (1 / (8 * (L j : ℝ)))
      = ∑ i ∈ Finset.Ico I₀ (I + 1), (1 / (8 * ((i : ℝ) + 1))) := by
  induction I, hI₀ using Nat.le_induction with
  | base => rw [group_sum, Nat.Ico_succ_singleton, Finset.sum_singleton]
  | succ I hI ih =>
      have h1 : (2:ℕ) ^ I₀ ≤ 2 ^ (I + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (2:ℕ) ^ (I + 1) ≤ 2 ^ (I + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← Finset.sum_Ico_consecutive _ h1 h2, ih, group_sum (I + 1),
        Finset.sum_Ico_succ_top (by omega : I₀ ≤ I + 1)]

/-- A tail of the harmonic series exceeds any bound. -/
theorem exists_harmonic_ge (I₀ : ℕ) (b : ℝ) :
    ∃ I, I₀ ≤ I ∧ b ≤ ∑ i ∈ Finset.Ico I₀ (I + 1), (1 / (8 * ((i : ℝ) + 1))) := by
  have key := Real.tendsto_sum_range_one_div_nat_succ_atTop
  have h := (tendsto_atTop.1 key
    (8 * b + ∑ i ∈ Finset.range I₀, (1 / (i + 1) : ℝ))).and (eventually_ge_atTop (I₀ + 1))
  obtain ⟨n, hn, hn'⟩ := h.exists
  refine ⟨n - 1, by omega, ?_⟩
  rw [show n - 1 + 1 = n by omega]
  have hsplit : ∑ i ∈ Finset.range I₀, (1 / (i + 1) : ℝ)
      + ∑ i ∈ Finset.Ico I₀ n, (1 / (i + 1) : ℝ)
      = ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  have hfac : ∑ i ∈ Finset.Ico I₀ n, (1 / (8 * ((i : ℝ) + 1)))
      = (1 / 8) * ∑ i ∈ Finset.Ico I₀ n, (1 / (i + 1) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (0:ℝ) < (i : ℝ) + 1 := by positivity
    field_simp
  rw [hfac]
  linarith only [hn, hsplit]

/-- The sums of the block probabilities over `[J, K]` tend to infinity with `K`. -/
theorem sum_p_tendsto (hp : ∀ j, 1 / (8 * (L j : ℝ)) ≤ p j) (hp0 : ∀ j, 0 ≤ p j) (J : ℕ) :
    Tendsto (fun K ↦ ∑ j ∈ Finset.Icc J K, p j) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ?_
  obtain ⟨I, hI, hIb⟩ := exists_harmonic_ge J b
  refine ⟨2 ^ (I + 1), fun K hK => ?_⟩
  have hsub : Finset.Ico (2 ^ J) (2 ^ (I + 1)) ⊆ Finset.Icc J K := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_Icc]
    have hJ : J ≤ 2 ^ J := Nat.le_of_lt (Nat.lt_two_pow_self)
    omega
  calc b ≤ ∑ i ∈ Finset.Ico J (I + 1), (1 / (8 * ((i : ℝ) + 1))) := hIb
    _ = ∑ j ∈ Finset.Ico (2 ^ J) (2 ^ (I + 1)), (1 / (8 * (L j : ℝ))) := (block_sum J I hI).symm
    _ ≤ ∑ j ∈ Finset.Ico (2 ^ J) (2 ^ (I + 1)), p j := Finset.sum_le_sum fun j _ => hp j
    _ ≤ ∑ j ∈ Finset.Icc J K, p j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hp0 j

/-- The probability of missing every event `E j`, `J ≤ j ≤ K`, tends to `0` as `K → ∞`. -/
theorem prod_tendsto_zero (hp : ∀ j, 1 / (8 * (L j : ℝ)) ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    (hp0 : ∀ j, 0 ≤ p j) :
    ∀ J, Tendsto (fun K ↦ ∏ j ∈ Finset.Icc J K, (1 - p j)) atTop (nhds 0) := by
  intro J
  have hexp : ∀ K, ∏ j ∈ Finset.Icc J K, (1 - p j)
      ≤ Real.exp (-(∑ j ∈ Finset.Icc J K, p j)) := by
    intro K
    have h1 : ∏ j ∈ Finset.Icc J K, (1 - p j) ≤ ∏ j ∈ Finset.Icc J K, Real.exp (-(p j)) := by
      refine Finset.prod_le_prod (fun i _ => by linarith only [hp1 i]) (fun i _ => ?_)
      linarith only [Real.add_one_le_exp (-(p i))]
    have h2 : ∏ j ∈ Finset.Icc J K, Real.exp (-(p j))
        = Real.exp (-(∑ j ∈ Finset.Icc J K, p j)) := by
      rw [← Real.exp_sum]
      congr 1
      simp
    linarith only [h1, h2.le, h2.ge]
  have hnonneg : ∀ K, (0:ℝ) ≤ ∏ j ∈ Finset.Icc J K, (1 - p j) :=
    fun K => Finset.prod_nonneg fun i _ => by linarith only [hp1 i]
  have hto : Tendsto (fun K ↦ Real.exp (-(∑ j ∈ Finset.Icc J K, p j))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (sum_p_tendsto hp hp0 J)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hto hnonneg hexp

/-! ### Eventual comparisons with `√(N log N)` -/

theorem tendsto_log_natCast_atTop : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `(log N)^ε ≪ (log N)^{1/2}` for `ε < 1/2`: the first question's bound is beaten. -/
theorem eventually_log_pow_lt (ε C : ℝ) (hε : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.sqrt N * Real.log N ^ ε < (1 / 64) * Real.sqrt (N * Real.log N) := by
  have hpow : Tendsto (fun N : ℕ ↦ (Real.log N) ^ (1 / 2 - ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith only [hε])).comp tendsto_log_natCast_atTop
  filter_upwards [hpow.eventually_gt_atTop (64 * C),
    tendsto_log_natCast_atTop.eventually_gt_atTop 0, eventually_ge_atTop 1] with N hN1 hN2 hN3
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN3
  have hS : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsplit : Real.sqrt ((N : ℝ) * Real.log N)
      = Real.sqrt N * Real.log N ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul hNpos.le, Real.sqrt_eq_rpow (Real.log N)]
  have hexp : Real.log N ^ (1 / 2 : ℝ) = Real.log N ^ ε * Real.log N ^ (1 / 2 - ε) := by
    rw [← Real.rpow_add hN2]
    congr 1
    ring
  have hpos : 0 < Real.log N ^ ε := Real.rpow_pos_of_pos hN2 _
  rw [hsplit, hexp]
  nlinarith only [hN1, mul_pos hS hpos, hS, hpos]

/-- For every exponent `K`, `(log u)^K ≤ u^{1/4}` for large `u`. -/
theorem log_rpow_le_rpow (K : ℝ) : ∀ᶠ u : ℝ in atTop, Real.log u ^ K ≤ u ^ (1 / 4 : ℝ) := by
  set K' : ℝ := max K 1 with hK'def
  have hK'1 : (1:ℝ) ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  have hr : (0:ℝ) < 1 / (4 * K') := by positivity
  have hbound := (isLittleO_log_rpow_atTop hr).def (by norm_num : (0:ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (Real.exp 1), eventually_gt_atTop (0:ℝ)]
    with u hu hu1 hu0
  have hlog1 : (1:ℝ) ≤ Real.log u := (Real.le_log_iff_exp_le hu0).2 hu1
  have hle : Real.log u ≤ u ^ (1 / (4 * K')) := by
    have h1 : ‖Real.log u‖ ≤ 1 * ‖u ^ (1 / (4 * K'))‖ := hu
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hu0.le _)] at h1
    exact le_trans (le_abs_self _) h1
  calc Real.log u ^ K ≤ Real.log u ^ K' := Real.rpow_le_rpow_of_exponent_le hlog1 hKK'
    _ ≤ (u ^ (1 / (4 * K'))) ^ K' :=
        Real.rpow_le_rpow (by linarith only [hlog1]) hle (by linarith only [hK'1])
    _ = u ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_mul hu0.le]
        congr 1
        field_simp

/-- `(log log N)^K ≪ (log N)^{1/2}`: the second question's bound is beaten. -/
theorem eventually_loglog_pow_lt (K C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.sqrt N * Real.log (Real.log N) ^ K < (1 / 64) * Real.sqrt (N * Real.log N) := by
  have hC' : (0:ℝ) < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCC' : C ≤ max C 1 := le_max_left _ _
  have hcomp : ∀ᶠ N : ℕ in atTop, Real.log (Real.log N) ^ K ≤ (Real.log N) ^ (1 / 4 : ℝ) :=
    tendsto_log_natCast_atTop.eventually (log_rpow_le_rpow K)
  filter_upwards [hcomp, eventually_log_pow_lt (1 / 4) (max C 1) (by norm_num),
    tendsto_log_natCast_atTop.eventually_gt_atTop 1] with N hab hlt hlog1
  have hS : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg _
  have ha : (0:ℝ) ≤ Real.log (Real.log N) ^ K :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith only [hlog1])) _
  calc C * Real.sqrt N * Real.log (Real.log N) ^ K
      ≤ max C 1 * Real.sqrt N * Real.log (Real.log N) ^ K :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hS) ha
    _ ≤ max C 1 * Real.sqrt N * Real.log N ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg hC'.le hS)
    _ < (1 / 64) * Real.sqrt (N * Real.log N) := hlt

end Erdos992
