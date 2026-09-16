import MerLeanExperiment.HighFrequencyCoherence
import MerLeanExperiment.SquareTestProducts
import MerLeanExperiment.FactorDivisibility
import MerLeanExperiment.FarResidue
import MerLeanExperiment.ChoosePowerBounds
import MerLeanExperiment.FrequencySummation

namespace ReciprocalSquares

open scoped BigOperators

/-- The uniform constant in the high-frequency energy estimate. -/
noncomputable def highFrequencyConstant : ℝ := 1 / (4 * (Nat.factorial 20 : ℝ) * 16 ^ 40)

noncomputable def badPrimeSubsets (N : ℕ) (h : ℤ) (T : Finset ℕ) : Finset (Finset ℕ) :=
  T.powersetCard 20 \ goodPrimeSubsets N h T

/-- Bad bottom-prime subsets give a concrete separated family of denominators. -/
theorem bad_prime_subsets_energy_lower (N : ℕ) (hN : 3 ≤ N) (h : ℤ) :
    ((badPrimeSubsets N h (widePrimes N)).card : ℝ) *
        ((N : ℝ) ^ 36 / (16 ^ 20 * (N : ℝ) ^ 40)) ^ 2 ≤
      residueEnergy (squareD N) (fun d => (h : ℝ) / (d : ℝ)) := by
  classical
  let B := badPrimeSubsets N h (widePrimes N)
  let E := B.image (fun S => (S.prod id) ^ 2)
  have hT : widePrimes N ⊆ largePrimes N := widePrimes_subset_largePrimes N hN
  have hBS : ∀ S ∈ B, S ⊆ widePrimes N ∧ S.card = 20 := by
    intro S hS
    exact Finset.mem_powersetCard.mp (Finset.mem_sdiff.mp hS).1
  have hinj : Set.InjOn (fun S : Finset ℕ => (S.prod id) ^ 2) (↑B : Set (Finset ℕ)) := by
    intro S hS T hT' heq
    exact square_subproduct_injOn N (by omega)
      (Finset.mem_powerset.mpr ((hBS S hS).1.trans hT))
      (Finset.mem_powerset.mpr ((hBS T hT').1.trans hT)) heq
  have hEcard : E.card = B.card := Finset.card_image_of_injOn hinj
  have hEsub : E ⊆ squareD N := by
    intro d hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    exact square_subproduct_mem_squareD N (by omega) S ((hBS S hS).1.trans hT)
      (Finset.card_pos.mp (by rw [(hBS S hS).2]; decide))
  have hbounds : ∀ d ∈ E, 0 < d ∧ (d : ℝ) ≤ 16 ^ 20 * (N : ℝ) ^ 40 := by
    intro d hd
    have hdpos : 0 < d := lt_trans Nat.zero_lt_one (squareD_members N (by omega) d (hEsub hd)).1
    refine ⟨hdpos, ?_⟩
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    have hprod : S.prod id ≤ (4 * N) ^ 20 := by
      have hb : ∀ p ∈ S, id p ≤ 4 * N := by
        intro p hp
        exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp ((hBS S hS).1 hp)).1).1
      simpa only [(hBS S hS).2] using Finset.prod_le_pow_card S id (4 * N) hb
    have hsq : (S.prod id) ^ 2 ≤ 16 ^ 20 * N ^ 40 := by
      calc
        (S.prod id) ^ 2 ≤ ((4 * N) ^ 20) ^ 2 := Nat.pow_le_pow_left hprod 2
        _ = 16 ^ 20 * N ^ 40 := by ring
    exact_mod_cast hsq
  have hfar : ∀ d ∈ E, ∀ z : ℤ,
      (N : ℝ) ^ 36 ≤ |(h : ℝ) - (d : ℝ) * (z : ℝ)| := by
    intro d hd z
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    have hnot := (Finset.mem_sdiff.mp hS).2
    have hstrict : ((N ^ 36 : ℕ) : ℤ) < |h - (((S.prod id) ^ 2 : ℕ) : ℤ) * z| := by
      by_contra hn
      apply hnot
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_sdiff.mp hS).1, ?_⟩
      exact ⟨(((S.prod id) ^ 2 : ℕ) : ℤ) * z, dvd_mul_right _ _, le_of_not_gt hn⟩
    exact_mod_cast hstrict.le
  have henergy := residueEnergy_ge_card_mul_far_ratio_sq (squareD N) E (h : ℝ)
    ((N : ℝ) ^ 36) (16 ^ 20 * (N : ℝ) ^ 40) hEsub (by positivity)
    (by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      positivity)
    hbounds hfar
  simpa only [hEcard] using henergy

/-- A coherent prime family and a missing construction factor give a uniform
nineteen-subset contribution to the residue energy. -/
theorem missing_factor_energy_lower (N : ℕ) (hN : 2 ≤ N) (h M : ℤ)
    (G : Finset ℕ) (hG : G ⊆ largePrimes N)
    (hdiv : ∀ p ∈ G, ((p ^ 2 : ℕ) : ℤ) ∣ M)
    (hnear : |h - M| ≤ (N ^ 36 : ℕ))
    (b : ℕ) (hb : b ∈ squareB N ∪ squareQ N) (hmissing : ¬ (b : ℤ) ∣ M) :
    (G.card.choose 19 : ℝ) * (1 / (4 * (N : ℝ) ^ 12)) ≤
      residueEnergy (squareD N) (fun d => (h : ℝ) / (d : ℝ)) := by
  classical
  let E := squareTestProducts b G 19
  have hEsub : E ⊆ squareD N :=
    squareTestProducts_subset_squareD N hN b hb G hG M hdiv hmissing 19 (by decide)
  have hEcard : E.card = G.card.choose 19 := squareTestProducts_card N hN b hb G hG 19
  have hbpos := square_factor_pos hb
  have hbbound : b ≤ N ^ 6 := by
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (squareB_bounds hb).2
    · exact (squareQ_bounds hb).2
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hden : 4 * (b : ℝ) ^ 2 ≤ 4 * (N : ℝ) ^ 12 := by
    have hbRbound : (b : ℝ) ≤ (N : ℝ) ^ 6 := by exact_mod_cast hbbound
    calc
      4 * (b : ℝ) ^ 2 ≤ 4 * ((N : ℝ) ^ 6) ^ 2 := by gcongr
      _ = 4 * (N : ℝ) ^ 12 := by ring
  have hterm : ∀ d ∈ E, 1 / (4 * (N : ℝ) ^ 12) ≤
      ((h : ℝ) / (d : ℝ) - (round ((h : ℝ) / (d : ℝ)) : ℝ)) ^ 2 := by
    intro d hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hSG, hScard⟩ := Finset.mem_powersetCard.mp hS
    have hSP : ((S.prod id) ^ 2 : ℕ) ∣ M.natAbs :=
      prime_square_product_dvd S M.natAbs
        (fun p hp => largePrimes_prime (hG (hSG hp)))
        (fun p hp => Int.natCast_dvd.mp (hdiv p (hSG hp)))
    have hsep := prime_prefix_square_separation N hN S (hSG.trans hG) hScard
    have hPpos : 0 < (S.prod id) ^ 2 := by omega
    have hscale : 2 * ((N ^ 36 : ℕ) : ℤ) ≤ (((S.prod id) ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hsep.le
    have hres := missing_factor_residue_sq_lower h M (N ^ 36 : ℕ) b ((S.prod id) ^ 2)
      hbpos hPpos (Int.natCast_dvd.mpr hSP) hmissing hnear hscale
    exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 4 * (b : ℝ) ^ 2) hden).trans hres
  calc
    (G.card.choose 19 : ℝ) * (1 / (4 * (N : ℝ) ^ 12)) =
        ∑ _d ∈ E, (1 : ℝ) / (4 * (N : ℝ) ^ 12) := by simp [hEcard]
    _ ≤ ∑ d ∈ E, ((h : ℝ) / (d : ℝ) - (round ((h : ℝ) / (d : ℝ)) : ℝ)) ^ 2 :=
      Finset.sum_le_sum hterm
    _ ≤ residueEnergy (squareD N) (fun d => (h : ℝ) / (d : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hEsub (by intros; positivity)

/-- Cancellation of the integer-power scales in the bad-subset contribution. -/
theorem high_frequency_bad_algebra (x C : ℝ) (hx : 0 < x)
    (hcount : x ^ 180 ≤ 4 * (Nat.factorial 20 : ℝ) * C) :
    highFrequencyConstant * x ^ 100 ≤
      C * (x ^ 360 / (16 ^ 20 * x ^ 400)) ^ 2 := by
  have hc : x ^ 180 / (4 * (Nat.factorial 20 : ℝ)) ≤ C := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  calc
    highFrequencyConstant * x ^ 100 =
        (x ^ 180 / (4 * (Nat.factorial 20 : ℝ))) *
          (x ^ 360 / (16 ^ 20 * x ^ 400)) ^ 2 := by
      unfold highFrequencyConstant
      field_simp [hx.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

/-- Cancellation of the integer-power scales in the missing-factor contribution. -/
theorem high_frequency_good_algebra (x C : ℝ) (hx : 0 < x)
    (hcount : x ^ 171 ≤ (Nat.factorial 19 : ℝ) * C) :
    highFrequencyConstant * x ^ 51 ≤ C * (1 / (4 * x ^ 120)) := by
  have hc : x ^ 171 / (Nat.factorial 19 : ℝ) ≤ C := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hconst : highFrequencyConstant ≤ 1 / (4 * (Nat.factorial 19 : ℝ)) := by
    norm_num [highFrequencyConstant, Nat.factorial]
  calc
    highFrequencyConstant * x ^ 51 ≤ (1 / (4 * (Nat.factorial 19 : ℝ))) * x ^ 51 :=
      mul_le_mul_of_nonneg_right hconst (pow_nonneg hx.le _)
    _ = (x ^ 171 / (Nat.factorial 19 : ℝ)) * (1 / (4 * x ^ 120)) := by
      field_simp [hx.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- Concrete uniform residue energy at every centered high frequency. -/
theorem high_frequency_energy_lower (M : ℕ) (hM : 262144 ≤ M) (h : ℤ)
    (hlo : (((M ^ 10) ^ 36 : ℕ) : ℤ) < |h|)
    (hcenter : 2 * |h| ≤ (squareModulus (M ^ 10) : ℤ)) :
    highFrequencyConstant * (M : ℝ) ^ 51 ≤
      residueEnergy (squareD (M ^ 10)) (fun d => (h : ℝ) / (d : ℝ)) := by
  classical
  let N := M ^ 10
  let R := M ^ 9
  let T := widePrimes N
  let B := badPrimeSubsets N h T
  have hmNat : 1 ≤ M := by omega
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hmNat
  have hN : 3 ≤ N := by
    have hself : M ≤ M ^ 10 := le_self_pow₀ hmNat (by decide : (10 : ℕ) ≠ 0)
    dsimp [N]
    omega
  have hR : 20 ≤ R := by
    have hself : M ≤ M ^ 9 := le_self_pow₀ hmNat (by decide : (9 : ℕ) ≠ 0)
    dsimp [R]
    omega
  have hT : T ⊆ largePrimes N := widePrimes_subset_largePrimes N hN
  have hreserve : 4 * R ≤ T.card :=
    widePrimes_card_pure_power M N hM le_rfl (by
      change N ≤ 4 * N ^ 2
      nlinarith)
  by_cases hbad : (T.powersetCard 20).card ≤ 4 * B.card
  · have hchoose : R ^ 20 ≤ Nat.factorial 20 * (T.powersetCard 20).card := by
      simpa only [Finset.card_powersetCard] using
        pow_le_factorial_mul_choose R T.card 20 (by omega) (by omega)
    have hcountNat : M ^ 180 ≤ 4 * Nat.factorial 20 * B.card := by
      have hh : R ^ 20 ≤ 4 * Nat.factorial 20 * B.card := by
        calc
          R ^ 20 ≤ Nat.factorial 20 * (T.powersetCard 20).card := hchoose
          _ ≤ Nat.factorial 20 * (4 * B.card) := Nat.mul_le_mul_left _ hbad
          _ = _ := by ring
      simpa only [R, ← pow_mul] using hh
    have hcount : (M : ℝ) ^ 180 ≤ 4 * (Nat.factorial 20 : ℝ) * (B.card : ℝ) := by
      exact_mod_cast hcountNat
    have henergy := bad_prime_subsets_energy_lower N hN h
    have henergy' : (B.card : ℝ) *
        ((M : ℝ) ^ 360 / (16 ^ 20 * (M : ℝ) ^ 400)) ^ 2 ≤
        residueEnergy (squareD (M ^ 10)) (fun d => (h : ℝ) / (d : ℝ)) := by
      simpa only [B, T, N, Nat.cast_pow, ← pow_mul] using henergy
    have hconst : 0 ≤ highFrequencyConstant := by unfold highFrequencyConstant; positivity
    calc
      highFrequencyConstant * (M : ℝ) ^ 51 ≤ highFrequencyConstant * (M : ℝ) ^ 100 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm1 (by decide : 51 ≤ 100)) hconst
      _ ≤ (B.card : ℝ) * ((M : ℝ) ^ 360 / (16 ^ 20 * (M : ℝ) ^ 400)) ^ 2 :=
        high_frequency_bad_algebra (M : ℝ) (B.card : ℝ) hm0 hcount
      _ ≤ _ := henergy'
  · have hgoodsub : goodPrimeSubsets N h T ⊆ T.powersetCard 20 := by
      unfold goodPrimeSubsets
      exact Finset.filter_subset _ _
    have hpartition : B.card + (goodPrimeSubsets N h T).card = (T.powersetCard 20).card :=
      Finset.card_sdiff_add_card_eq_card hgoodsub
    have hdensity : 3 * (T.powersetCard 20).card ≤ 4 * (goodPrimeSubsets N h T).card := by
      omega
    obtain ⟨G, hGT, hGcard, L, hnear, hdiv⟩ :=
      exists_large_coherent_prime_subset N R h T (by omega) (by omega) hT hreserve hdensity
    obtain ⟨b, hb, hmissing⟩ :=
      exists_missing_factor_of_near N h L (N ^ 36 : ℕ) hlo hcenter hnear
    have henergy := missing_factor_energy_lower N (by omega) h L G (hGT.trans hT)
      hdiv hnear b hb hmissing
    have hchoose := pow_le_factorial_mul_choose R G.card 19 (by omega) hGcard
    have hcountNat : M ^ 171 ≤ Nat.factorial 19 * G.card.choose 19 := by
      simpa only [R, ← pow_mul] using hchoose
    have hcount : (M : ℝ) ^ 171 ≤ (Nat.factorial 19 : ℝ) * (G.card.choose 19 : ℝ) := by
      exact_mod_cast hcountNat
    have henergy' : (G.card.choose 19 : ℝ) * (1 / (4 * (M : ℝ) ^ 120)) ≤
        residueEnergy (squareD (M ^ 10)) (fun d => (h : ℝ) / (d : ℝ)) := by
      simpa only [N, Nat.cast_pow, ← pow_mul] using henergy
    exact (high_frequency_good_algebra (M : ℝ) (G.card.choose 19 : ℝ) hm0 hcount).trans henergy'

/-- The high-frequency energy estimate gives uniform centered-product decay. -/
theorem high_frequency_centeredProduct_norm_le
    (M : ℕ) (hM : 262144 ≤ M) (h : ℤ) (p κ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hκ0 : 0 ≤ κ) (hκ : κ ≤ p * (1 - p))
    (hlo : (((M ^ 10) ^ 36 : ℕ) : ℤ) < |h|)
    (hcenter : 2 * |h| ≤ (squareModulus (M ^ 10) : ℤ)) :
    ‖centeredProduct (squareD (M ^ 10)) p h‖ ≤
      Real.exp (-8 * κ * highFrequencyConstant * (M : ℝ) ^ 51) := by
  have henergy := high_frequency_energy_lower M hM h hlo hcenter
  have hbound := norm_centeredProduct_le_of_energy_lower (squareD (M ^ 10)) p κ
    (highFrequencyConstant * (M : ℝ) ^ 51) h hp0 hp1 hκ0 hκ henergy
  simpa only [mul_assoc] using hbound

end ReciprocalSquares
