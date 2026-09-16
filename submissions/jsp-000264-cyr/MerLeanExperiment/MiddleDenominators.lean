import MerLeanExperiment.SquareSubproducts

namespace ReciprocalSquares

/-- A minimal subproduct crosses the upper threshold without crossing the lower one. -/
theorem exists_balanced_subproduct (N R : ℕ) (T : Finset ℕ)
    (hR : N ≤ R) (hT : ∀ q ∈ T, 0 < q ∧ q ≤ 4 * N)
    (hfull : R < 4 * N ^ 2 * T.prod id) :
    ∃ S ⊆ T, 0 < S.prod id ∧ N * S.prod id ≤ R ∧
      R < 4 * N ^ 2 * S.prod id := by
  let C := T.powerset.filter (fun S => R < 4 * N ^ 2 * S.prod id)
  have hC : C.Nonempty := ⟨T, Finset.mem_filter.mpr ⟨by simp, hfull⟩⟩
  obtain ⟨S, hSC, hmin⟩ := C.exists_min_image Finset.card hC
  obtain ⟨hST, hupper⟩ := Finset.mem_filter.mp hSC
  have hsub : S ⊆ T := Finset.mem_powerset.mp hST
  have hpos : 0 < S.prod id := Finset.prod_pos (fun q hq => (hT q (hsub hq)).1)
  refine ⟨S, hsub, hpos, ?_, hupper⟩
  by_cases hempty : S = ∅
  · simpa [hempty] using hR
  · obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have herase : 4 * N ^ 2 * (S.erase q).prod id ≤ R := by
      by_contra hbad
      have hmem : S.erase q ∈ C := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.erase_subset q S).trans hsub), by omega⟩
      have hcard := hmin (S.erase q) hmem
      have hlt := Finset.card_erase_lt_of_mem hq
      omega
    have hqbound := (hT q (hsub hq)).2
    calc
      N * S.prod id = (N * q) * (S.erase q).prod id := by
        rw [← Finset.mul_prod_erase S id hq]
        simp only [id_eq]
        ring
      _ ≤ (4 * N ^ 2) * (S.erase q).prod id :=
        Nat.mul_le_mul_right _ (by nlinarith)
      _ ≤ R := herase

/-- The middle-frequency interval contains many distinct constructed denominators. -/
theorem exists_middle_denominators (M H : ℕ) (hM : 262144 ≤ M)
    (hlo : (M ^ 10) ^ 2 ≤ 2 * H) (hhi : H ≤ (M ^ 10) ^ 36) :
    ∃ E : Finset ℕ, E ⊆ squareD (M ^ 10) ∧ M ^ 9 ≤ E.card ∧
      ∀ d ∈ E, 2 * H < d ∧ d ≤ 32 * H := by
  let N := M ^ 10
  let R := Nat.sqrt (2 * H)
  have hNbig : 17 ≤ N := by
    have hself : M ≤ M ^ 10 := le_self_pow₀ (by omega) (by decide : (10 : ℕ) ≠ 0)
    dsimp [N]
    omega
  have hNpos : 0 < N := by omega
  have hM9 : 18 ≤ M ^ 9 := by
    have hself : M ≤ M ^ 9 := le_self_pow₀ (by omega) (by decide : (9 : ℕ) ≠ 0)
    omega
  have hreserve : 4 * M ^ 9 ≤ (widePrimes N).card :=
    widePrimes_card_pure_power M N hM le_rfl (by change N ≤ 4 * N ^ 2; nlinarith)
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
    (show 18 ≤ (widePrimes N).card by omega)
  have hTbounds : ∀ q ∈ T, N < q ∧ q ≤ 4 * N := by
    intro q hq
    obtain ⟨hq4, hqnot⟩ := Finset.mem_sdiff.mp (hTsub hq)
    obtain ⟨hqle, hqprime⟩ := Nat.mem_primesLE.mp hq4
    refine ⟨?_, hqle⟩
    by_contra hbad
    exact hqnot (Nat.mem_primesLE.mpr ⟨by omega, hqprime⟩)
  have hTlarge : T ⊆ largePrimes N :=
    hTsub.trans (widePrimes_subset_largePrimes N (by omega))
  have hprod : N ^ 18 ≤ T.prod id := by
    calc
      N ^ 18 = ∏ _q ∈ T, N := by simp [hTcard]
      _ ≤ T.prod id := Finset.prod_le_prod (fun _ _ => Nat.zero_le N)
        (fun q hq => (hTbounds q hq).1.le)
  have hRN : N ≤ R := Nat.le_sqrt'.mpr hlo
  have hRupper : R < 2 * N ^ 18 := by
    apply Nat.sqrt_lt'.mpr
    have hpow : (N ^ 18) ^ 2 = N ^ 36 := by ring
    have hpowpos : 0 < N ^ 36 := pow_pos hNpos 36
    change H ≤ N ^ 36 at hhi
    nlinarith
  have hfull : R < 4 * N ^ 2 * T.prod id := by
    apply hRupper.trans_le
    calc
      2 * N ^ 18 ≤ (4 * N ^ 2) * N ^ 18 :=
        Nat.mul_le_mul_right _ (by nlinarith)
      _ ≤ 4 * N ^ 2 * T.prod id := Nat.mul_le_mul_left _ hprod
  obtain ⟨S, hST, hSpos, hSlo, hShi⟩ := exists_balanced_subproduct N R T hRN
    (fun q hq => ⟨lt_trans hNpos (hTbounds q hq).1, (hTbounds q hq).2⟩) hfull
  let P := S.prod id
  let K := R / P
  have hPpos : 0 < P := hSpos
  have hKlo : N ≤ K := (Nat.le_div_iff_mul_le hPpos).mpr hSlo
  have hKhi : K < 4 * N ^ 2 := (Nat.div_lt_iff_lt_mul hPpos).mpr hShi
  have hKreserve : 4 * M ^ 9 ≤ (widePrimes K).card :=
    widePrimes_card_pure_power M K hM hKlo hKhi.le
  let Q := widePrimes K \ T
  have hQcard : M ^ 9 ≤ Q.card := by
    have hcard := Finset.card_le_card_sdiff_add_card (s := widePrimes K) (t := T)
    change (widePrimes K).card ≤ Q.card + T.card at hcard
    omega
  have hQbounds : ∀ p ∈ Q, K < p ∧ p ≤ 4 * K ∧ p ∉ T := by
    intro p hp
    obtain ⟨hpwide, hpT⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp4, hpnot⟩ := Finset.mem_sdiff.mp hpwide
    obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp4
    refine ⟨?_, hpbound, hpT⟩
    by_contra hbad
    exact hpnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
  have hQlarge : Q ⊆ largePrimes N := by
    intro p hp
    obtain ⟨hpK, hp4, _⟩ := hQbounds p hp
    have hpprime : p.Prime :=
      (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1).2
    have hNcube : 16 * N ^ 2 < N ^ 3 := by
      calc
        16 * N ^ 2 < N * N ^ 2 :=
          Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos hNpos 2)
        _ = N ^ 3 := by ring
    have hpupper : p < N ^ 3 := by
      apply lt_trans _ hNcube
      nlinarith
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨hpupper, hpprime⟩, lt_of_le_of_lt hKlo hpK⟩
  let f : ℕ → ℕ := fun p => (P * p) ^ 2
  let E := Q.image f
  have hinj : Function.Injective f := by
    intro p q hpq
    have heq : P * p = P * q := Nat.pow_left_injective (by decide : 2 ≠ 0) hpq
    exact Nat.eq_of_mul_eq_mul_left hPpos heq
  refine ⟨E, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    have hpnotS : p ∉ S := fun hs => (hQbounds p hp).2.2 (hST hs)
    have hsub : insert p S ⊆ largePrimes N := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hqS
      · exact hQlarge hp
      · exact hTlarge (hST hqS)
    have hmem := square_subproduct_mem_squareD N (by omega) (insert p S) hsub
      (Finset.insert_nonempty p S)
    simpa only [Finset.prod_insert hpnotS, id_eq, mul_comm, P, f] using hmem
  · simpa only [E, Finset.card_image_of_injective Q hinj] using hQcard
  · intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hpK, hp4, _⟩ := hQbounds p hp
    have hlowroot : R < P * p := by
      have := (Nat.div_lt_iff_lt_mul hPpos).mp hpK
      simpa only [mul_comm] using this
    have hupproot : P * p ≤ 4 * R := by
      calc
        P * p ≤ P * (4 * K) := Nat.mul_le_mul_left P hp4
        _ = 4 * (K * P) := by ring
        _ ≤ 4 * R := Nat.mul_le_mul_left 4 (Nat.div_mul_le_self R P)
    constructor
    · exact Nat.sqrt_lt'.mp hlowroot
    · change (P * p) ^ 2 ≤ 32 * H
      calc
        (P * p) ^ 2 ≤ (4 * R) ^ 2 := Nat.pow_le_pow_left hupproot 2
        _ = 16 * R ^ 2 := by ring
        _ ≤ 16 * (2 * H) := Nat.mul_le_mul_left 16 (Nat.sqrt_le' (2 * H))
        _ = 32 * H := by ring

end ReciprocalSquares
