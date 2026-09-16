import MerLeanExperiment.ColorResidual
import MerLeanExperiment.BernoulliParameters
import MerLeanExperiment.LargeScale
import MerLeanExperiment.SquareFourierEstimate
import MerLeanExperiment.FourierCounting
import MerLeanExperiment.ResidualCollision

namespace ReciprocalSquares

/-- Every nontrivial partition of the square denominators greater than one
has equal nonempty reciprocal sums in its two colors. -/
theorem square_partition
    (X : Set ℕ)
    (hX : ∃ n : ℕ, 1 < n ∧ IsSquare n ∧ n ∈ X)
    (hY : ∃ n : ℕ, 1 < n ∧ IsSquare n ∧ n ∉ X) :
    ∃ A B : Finset ℕ, A.Nonempty ∧ B.Nonempty ∧
      (∀ n ∈ A, 1 < n ∧ IsSquare n ∧ n ∈ X) ∧
      (∀ n ∈ B, 1 < n ∧ IsSquare n ∧ n ∉ X) ∧
      (∑ n ∈ A, (1 : ℚ) / n) = ∑ n ∈ B, (1 : ℚ) / n := by
  classical
  obtain ⟨x, hxgt, hxsq, hxX⟩ := hX
  obtain ⟨y, hygt, hysq, hyX⟩ := hY
  let ε : ℚ := 1 / (10 * (x : ℚ))
  let c : ℚ := 1 + ε / 8
  let A : ℚ := max (y : ℚ) (c / ε)
  have hxQ : (0 : ℚ) < x := by exact_mod_cast (show 0 < x by omega)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 1 < c := by dsimp [c]; linarith
  have hAy : (y : ℚ) ≤ A := le_max_left _ _
  have hA : 1 < A := lt_of_lt_of_le (by exact_mod_cast hygt) hAy
  have hcap : c ≤ ε * A := by
    have h := le_max_right (y : ℚ) (c / ε)
    have := (div_le_iff₀ hε).mp h
    simpa only [mul_comm] using this
  let κ : ℝ := ((c : ℝ) - 1) / ((A : ℝ) * (c : ℝ))
  let q : ℝ := max (1 - 1 / (A : ℝ)) (1 / (c : ℝ))
  have hcR : (1 : ℝ) < c := by exact_mod_cast hc
  have hAR : (1 : ℝ) < A := by exact_mod_cast hA
  have hcR0 : (0 : ℝ) < c := by linarith
  have hAR0 : (0 : ℝ) < A := by linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hq0 : 0 < q := (one_div_pos.mpr hcR0).trans_le (le_max_right _ _)
  have hq1 : q < 1 := by
    apply max_lt
    · have := one_div_pos.mpr hAR0
      linarith
    · exact (div_lt_one hcR0).mpr hcR
  have hlam : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hC : 0 < highFrequencyConstant := by unfold highFrequencyConstant; positivity
  obtain ⟨M, hMB, hM, hεscale, hatomScale, hhighScale, htail⟩ :=
    exists_large_scale (ε : ℝ) κ (-Real.log q) highFrequencyConstant
      (by exact_mod_cast hε) hκ hlam hC (max x y)
  let N := M ^ 10
  have hMN : M ≤ N := le_self_pow₀ (by omega) (by decide : (10 : ℕ) ≠ 0)
  have hN : 20 < N := by omega
  let Z := (squareZ N).erase 1
  let Y := oppositeColor Z X
  let D := squareD N
  let m := squareModulus N
  have hxZ : x ∈ Z := square_mem_squareZ_erase_one_of_le N x (by omega)
    hxgt hxsq ((le_max_left x y).trans (hMB.trans hMN))
  have hyZ : y ∈ Z := square_mem_squareZ_erase_one_of_le N y (by omega)
    hygt hysq ((le_max_right x y).trans (hMB.trans hMN))
  have hεN : (3 : ℚ) ≤ ε ^ 2 * (N : ℚ) := by
    change (3 : ℚ) ≤ ε ^ 2 * ((M ^ 10 : ℕ) : ℚ)
    exact_mod_cast hεscale
  obtain ⟨S, hSE, hrpos, hrlow, hrhigh⟩ := exists_color_residual N x y X ε A
    hN hxZ hxX hyZ hyX hε le_rfl hεN hAy hcap
  let r : ℚ := recipSumQ Y - recipSumQ S
  let W : ℚ := recipSumQ D
  have hr0 : 0 < r := hrpos
  have hcW : c * r < W := hrlow
  have hWA : W ≤ A * r := hrhigh
  have hrW : r < W := by nlinarith
  have hW1 : W < 1 := lt_of_le_of_lt
    (recipSumQ_square_le_three_quarters D (squareD_members N (by omega))) (by norm_num)
  have hS : S ⊆ Z := by
    intro d hd
    obtain ⟨hd1, hdE⟩ := Finset.mem_erase.mp (hSE hd)
    exact Finset.mem_erase.mpr ⟨hd1, squareE_subset_squareZ N (by omega) hdE⟩
  have hDZ : D ⊆ Z := by
    intro d hd
    exact Finset.mem_erase.mpr
      ⟨by have := (squareD_members N (by omega) d hd).1; omega,
        (Finset.mem_sdiff.mp hd).1⟩
  have hYsub : Y ⊆ Z := Finset.filter_subset _ _
  have hreserve := widePrimes_card_pure_power M N hM le_rfl (by
    change N ≤ 4 * N ^ 2
    nlinarith)
  have hprimes : (widePrimes N).Nonempty := Finset.card_pos.mp (by
    have : 0 < M ^ 9 := pow_pos (by omega : 0 < M) 9
    omega)
  obtain ⟨p₀, hp₀⟩ := hprimes
  have hdivZ : ∀ z ∈ Z, z ∣ m := by
    intro z hz
    exact squareZ_dvd_squareD_lcm N p₀ (by omega)
      (widePrimes_subset_largePrimes N (by omega) hp₀) z (Finset.mem_of_mem_erase hz)
  obtain ⟨k, _hkpos, hk⟩ := exists_pos_residual_numerator Z Y S m
    (squareModulus_pos N)
    (fun z hz => by have := (squareZ_erase_one_members N z hz).1; omega)
    hdivZ hYsub hS hr0
  let p : ℝ := (r : ℝ) / (W : ℝ)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hcWR : (c : ℝ) * (r : ℝ) < W := by exact_mod_cast hcW
  have hWAR : (W : ℝ) ≤ (A : ℝ) * (r : ℝ) := by exact_mod_cast hWA
  obtain ⟨_, _, hp0, hp1, _, _⟩ :=
    bernoulli_ratio_bounds (c : ℝ) (A : ℝ) (r : ℝ) (W : ℝ) hcR hrR hcWR hWAR
  have hvariance : κ ≤ p * (1 - p) :=
    (bernoulli_variance_lower (c : ℝ) (A : ℝ) (r : ℝ) (W : ℝ)
      hcR hrR hcWR hWAR).2
  have hmax : max p (1 - p) ≤ q :=
    (bernoulli_atom_bound (c : ℝ) (A : ℝ) (r : ℝ) (W : ℝ)
      hcR hrR hcWR hWAR).2.2
  have hAtom : (max p (1 - p)) ^ D.card < 1 / (2 * (m : ℝ)) :=
    (pow_le_pow_left₀ (hp0.le.trans (le_max_left _ _)) hmax _).trans_lt
      (squareD_atom_lt_half_modulus M hM q hq0 hq1 hatomScale)
  have hFourier := square_centered_fourier_sum_ge_half M hM p κ
    hp0.le hp1.le hκ hvariance hhighScale htail
  obtain ⟨U, hU, V, hV, hUV, hUr, hVr⟩ := exists_two_subsets_of_centered_sum
    D m k r p
    (fun d hd => by have := (squareD_members N (by omega) d hd).1; omega)
    (fun d hd => Finset.dvd_lcm hd) hW1 hr0 hrW hk rfl hFourier hAtom
  have hdisj (T : Finset ℕ) (hT : T ⊆ D) : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro d hdS hdT
    exact (Finset.mem_sdiff.mp (hT hdT)).2 (Finset.mem_of_mem_erase (hSE hdS))
  apply partition_collision_of_two_residual_representations Z S U V X r
    (squareZ_erase_one_members N) hS (hU.trans hDZ) (hV.trans hDZ)
    (hdisj U hU) (hdisj V hV) hUV hUr hVr
  rfl

end ReciprocalSquares
