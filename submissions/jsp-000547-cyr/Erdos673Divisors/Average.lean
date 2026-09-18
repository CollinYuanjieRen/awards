import Erdos673Divisors.Basic

/-!
# Erdős Problem 673 — `G` grows on average

The average of `G` over `[1, X]` tends to infinity.  The route is elementary: for even `n = 2k`
one has `G(2k) ≥ τ(2k)/4 ≥ τ(k)/4` (`card_divisors_le_mul_G` with `p = 2`, plus
`τ(k) ≤ τ(2k)`), so `∑_{n ≤ X} G n ≥ (1/4) ∑_{k ≤ X/2} τ(k)`; and double counting gives
`∑_{k ≤ Y} τ(k) = ∑_{d ≤ Y} ⌊Y/d⌋ ≥ Y·(H_Y − 1) ≥ Y·(log (Y+1) − 1)`.

Main results: `sum_card_divisors_ge`, `sum_G_ge`, `erdos_673_average`.
-/

namespace Erdos673

open Finset

/-- Double counting: `∑_{k ≤ Y} τ(k) = ∑_{d ≤ Y} ⌊Y/d⌋`. -/
theorem sum_card_divisors_eq_sum_div (Y : ℕ) :
    ∑ k ∈ Finset.Icc 1 Y, (Nat.divisors k).card = ∑ d ∈ Finset.Icc 1 Y, Y / d := by
  classical
  have hIcc : Finset.Icc 1 Y = Finset.Ioc 0 Y := rfl
  have hrow : ∀ k ∈ Finset.Icc 1 Y,
      (Nat.divisors k).card = ∑ d ∈ Finset.Icc 1 Y, if d ∣ k then 1 else 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← Finset.card_filter]
    congr 1
    refine Finset.ext ?_
    intro d
    constructor
    · intro hmem
      have hdk : d ∣ k := (Nat.mem_divisors.mp hmem).1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hmem
      have hdk' : d ≤ k := Nat.le_of_dvd (by omega) hdk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos, by omega⟩, hdk⟩
    · intro hmem
      rcases Finset.mem_filter.mp hmem with ⟨-, hdk⟩
      exact Nat.mem_divisors.mpr ⟨hdk, by omega⟩
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [← Finset.card_filter, hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div Y d

/-- `∑_{k ≤ Y} τ(k) ≥ Y·(log (Y+1) − 1)`. -/
theorem sum_card_divisors_ge (Y : ℕ) :
    (Y : ℝ) * (Real.log (Y + 1) - 1) ≤ ∑ k ∈ Finset.Icc 1 Y, ((Nat.divisors k).card : ℝ) := by
  have key : (∑ k ∈ Finset.Icc 1 Y, ((Nat.divisors k).card : ℝ))
      = ∑ d ∈ Finset.Icc 1 Y, ((Y / d : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (sum_card_divisors_eq_sum_div Y)
  rw [key]
  have hH : ((harmonic Y : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 Y, ((i : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    ring
  have hlog : Real.log ((Y : ℝ) + 1) ≤ ((harmonic Y : ℚ) : ℝ) := by
    have := log_add_one_le_harmonic Y
    push_cast at this ⊢
    linarith
  have hsplit : ∑ d ∈ Finset.Icc 1 Y, ((Y : ℝ) * (d : ℝ)⁻¹ - 1)
      = (Y : ℝ) * (∑ i ∈ Finset.Icc 1 Y, ((i : ℝ))⁻¹) - (Y : ℝ) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc]
    simp
  have hterm : ∀ d ∈ Finset.Icc 1 Y, (Y : ℝ) * (d : ℝ)⁻¹ - 1 ≤ ((Y / d : ℕ) : ℝ) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      have : 0 < d := by omega
      exact_mod_cast this
    have hnat : Y < d * (Y / d) + d := by
      have h1 := Nat.div_add_mod Y d
      have h2 := Nat.mod_lt Y (show 0 < d by omega)
      omega
    have hR : (Y : ℝ) < (d : ℝ) * ((Y / d : ℕ) : ℝ) + (d : ℝ) := by exact_mod_cast hnat
    have hdiv : (Y : ℝ) / (d : ℝ) ≤ ((Y / d : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hdpos]
      linarith [hR]
    rw [← div_eq_mul_inv]
    linarith
  calc (Y : ℝ) * (Real.log ((Y : ℝ) + 1) - 1)
      ≤ (Y : ℝ) * (((harmonic Y : ℚ) : ℝ) - 1) := by
        have hY : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
        nlinarith [hlog]
    _ = (Y : ℝ) * (∑ i ∈ Finset.Icc 1 Y, ((i : ℝ))⁻¹) - (Y : ℝ) := by rw [hH]; ring
    _ = ∑ d ∈ Finset.Icc 1 Y, ((Y : ℝ) * (d : ℝ)⁻¹ - 1) := hsplit.symm
    _ ≤ ∑ d ∈ Finset.Icc 1 Y, ((Y / d : ℕ) : ℝ) := Finset.sum_le_sum hterm

/-- Restricting to even numbers: `∑_{n ≤ X} G n ≥ (1/4) ∑_{k ≤ X/2} τ(k)`. -/
theorem sum_G_ge (X : ℕ) :
    (∑ k ∈ Finset.Icc 1 (X / 2), ((Nat.divisors k).card : ℝ)) / 4 ≤ ∑ n ∈ Finset.Icc 1 X, G n := by
  classical
  have hinj : Set.InjOn (fun k => 2 * k) ↑(Finset.Icc 1 (X / 2)) := by
    intro a _ b _ h
    simp only at h
    omega
  have hsub : (Finset.Icc 1 (X / 2)).image (fun k => 2 * k) ⊆ Finset.Icc 1 X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have h1 : ∑ n ∈ (Finset.Icc 1 (X / 2)).image (fun k => 2 * k), G n ≤ ∑ n ∈ Finset.Icc 1 X, G n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => G_nonneg i)
  rw [Finset.sum_image hinj] at h1
  refine le_trans ?_ h1
  rw [Finset.sum_div]
  refine Finset.sum_le_sum ?_
  intro k hk
  rw [Finset.mem_Icc] at hk
  have h2k : 0 < 2 * k := by omega
  have hG := card_divisors_le_mul_G h2k Nat.prime_two (dvd_mul_right 2 k)
  have hc : ((Nat.divisors k).card : ℝ) ≤ ((Nat.divisors (2 * k)).card : ℝ) := by
    exact_mod_cast card_divisors_le_card_divisors_two_mul k
  norm_num at hG
  linarith

/-- Erdős's "`G` grows on average": `(1/X) ∑_{n ≤ X} G n → ∞`. -/
theorem erdos_673_average :
    Filter.Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, G n) / X) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hMM' : M ≤ M' := le_max_left _ _
  refine ⟨max 2 ⌈4 * Real.exp (16 * M' + 1)⌉₊, ?_⟩
  intro X hX
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXceil : ⌈4 * Real.exp (16 * M' + 1)⌉₊ ≤ X := le_trans (le_max_right _ _) hX
  have hXR : 4 * Real.exp (16 * M' + 1) ≤ (X : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hXceil)
  set Y : ℕ := X / 2 with hY
  set A : ℝ := (X : ℝ) / 4 with hA
  have hApos : 0 < A := by
    have : (0 : ℝ) < (X : ℝ) := by
      have : (0 : ℕ) < X := by omega
      exact_mod_cast this
    rw [hA]; linarith
  have hAexp : Real.exp (16 * M' + 1) ≤ A := by rw [hA]; linarith
  have hlogA : 16 * M' + 1 ≤ Real.log A := (Real.le_log_iff_exp_le hApos).mpr hAexp
  have hY1 : 1 ≤ Y := by omega
  have hAY : A ≤ (Y : ℝ) := by
    have hnat : X ≤ 4 * Y := by omega
    have : (X : ℝ) ≤ 4 * (Y : ℝ) := by exact_mod_cast hnat
    rw [hA]; linarith
  have hlogY : Real.log A ≤ Real.log ((Y : ℝ) + 1) :=
    Real.log_le_log hApos (by linarith)
  have hstep : A * (16 * M') ≤ (Y : ℝ) * (Real.log ((Y : ℝ) + 1) - 1) := by
    have h1 : A * (16 * M') ≤ A * (Real.log ((Y : ℝ) + 1) - 1) := by
      have : 16 * M' ≤ Real.log ((Y : ℝ) + 1) - 1 := by linarith
      nlinarith
    have h2 : A * (Real.log ((Y : ℝ) + 1) - 1) ≤ (Y : ℝ) * (Real.log ((Y : ℝ) + 1) - 1) := by
      have hnn : 0 ≤ Real.log ((Y : ℝ) + 1) - 1 := by nlinarith
      nlinarith
    linarith
  have hsum := sum_card_divisors_ge Y
  have hG := sum_G_ge X
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    have : (0 : ℕ) < X := by omega
    exact_mod_cast this
  have hAX : A * (16 * M') = 4 * ((X : ℝ) * M') := by rw [hA]; ring
  have hfinal : M' * (X : ℝ) ≤ ∑ n ∈ Finset.Icc 1 X, G n := by
    have := hG
    rw [← hY] at this
    linarith
  rw [le_div_iff₀ hXpos]
  have hMX : M * (X : ℝ) ≤ M' * (X : ℝ) := mul_le_mul_of_nonneg_right hMM' hXpos.le
  linarith

end Erdos673
