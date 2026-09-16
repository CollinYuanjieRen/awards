import MerLeanExperiment.SquareFactorization
import MerLeanExperiment.PrimeReserve

namespace ReciprocalSquares

/-- The smooth base one is available for every scale used by the construction. -/
theorem one_mem_smoothRoots (N : ℕ) (hN : 2 ≤ N) : 1 ∈ smoothRoots N := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    have hself : N ≤ N ^ 3 := le_self_pow₀ (by omega) (by decide : (3 : ℕ) ≠ 0)
    omega
  · simp only [Nat.mem_smoothNumbers]
    exact ⟨by decide, by simp⟩

/-- Every nonempty large-prime subproduct survives erasure of smooth squares. -/
theorem square_subproduct_mem_squareD (N : ℕ) (hN : 2 ≤ N)
    (S : Finset ℕ) (hS : S ⊆ largePrimes N) (hne : S.Nonempty) :
    (S.prod id) ^ 2 ∈ squareD N := by
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨S.prod id, ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(1, S), Finset.mem_product.mpr
      ⟨one_mem_smoothRoots N hN, Finset.mem_powerset.mpr hS⟩, ?_⟩
    simp [rootProduct]
  · intro he
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp he
    have hprod : a = S.prod id := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) heq
    have hsmooth : a ∈ Nat.smoothNumbers (N + 1) := (Finset.mem_filter.mp ha).2
    obtain ⟨p, hp⟩ := hne
    have hpprime := largePrimes_prime (hS hp)
    have hpdiv : p ∣ a := by
      rw [hprod]
      exact Finset.dvd_prod_of_mem id hp
    have hsmall := Nat.mem_smoothNumbers'.mp hsmooth p hpprime hpdiv
    have hlarge : N < p := (Finset.mem_filter.mp (hS hp)).2
    omega

/-- Distinct subsets give distinct square denominators, including the empty subset. -/
theorem square_subproduct_injOn (N : ℕ) (hN : 2 ≤ N) :
    Set.InjOn (fun S : Finset ℕ => (S.prod id) ^ 2)
      (↑(largePrimes N).powerset : Set (Finset ℕ)) := by
  intro S hS T hT heq
  have hprod : S.prod id = T.prod id := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) heq
  have hpair : (1, S) = (1, T) := rootProduct_injOn N
    (Finset.mem_product.mpr ⟨one_mem_smoothRoots N hN, hS⟩)
    (Finset.mem_product.mpr ⟨one_mem_smoothRoots N hN, hT⟩)
    (by simpa [rootProduct] using hprod)
  exact congrArg Prod.snd hpair

/-- Every fixed positive subset size supplies distinct retained denominators. -/
theorem choose_le_squareD_card (N : ℕ) (hN : 2 ≤ N)
    (Q : Finset ℕ) (hQ : Q ⊆ largePrimes N) (k : ℕ) (hk : 1 ≤ k) :
    Q.card.choose k ≤ (squareD N).card := by
  let f : Finset ℕ → ℕ := fun S => (S.prod id) ^ 2
  have hinj : Set.InjOn f (↑(Q.powersetCard k) : Set (Finset ℕ)) := by
    intro S hS T hT heq
    apply square_subproduct_injOn N hN
      (Finset.mem_powerset.mpr ((Finset.mem_powersetCard.mp hS).1.trans hQ))
      (Finset.mem_powerset.mpr ((Finset.mem_powersetCard.mp hT).1.trans hQ)) heq
  have himage : (Q.powersetCard k).image f ⊆ squareD N := by
    intro d hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    apply square_subproduct_mem_squareD N hN S (hsub.trans hQ)
    exact Finset.card_pos.mp (by omega)
  calc
    Q.card.choose k = (Q.powersetCard k).card := (Finset.card_powersetCard k Q).symm
    _ = ((Q.powersetCard k).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (squareD N).card := Finset.card_le_card himage

/-- A loose fourth-power lower bound for the binomial coefficient. -/
theorem pow_four_le_twentyfour_choose (R K : ℕ) (hR : 1 ≤ R) (hK : 4 * R ≤ K) :
    R ^ 4 ≤ 24 * K.choose 4 := by
  have hsub : R ≤ K + 1 - 4 := by omega
  calc
    R ^ 4 ≤ (K + 1 - 4) ^ 4 := Nat.pow_le_pow_left hsub 4
    _ ≤ K.descFactorial 4 := Nat.pow_sub_le_descFactorial K 4
    _ = 24 * K.choose 4 := by rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num

/-- Four-element subsets already give enough denominators for the atom bound. -/
theorem pow_four_le_twentyfour_squareD_card
    (N : ℕ) (hN : 2 ≤ N) (Q : Finset ℕ) (hQ : Q ⊆ largePrimes N)
    (R : ℕ) (hR : 1 ≤ R) (hcard : 4 * R ≤ Q.card) :
    R ^ 4 ≤ 24 * (squareD N).card := by
  exact (pow_four_le_twentyfour_choose R Q.card hR hcard).trans
    (Nat.mul_le_mul_left 24 (choose_le_squareD_card N hN Q hQ 4 (by decide)))

/-- Bottom-interval primes fit into the construction's full large-prime set. -/
theorem widePrimes_subset_largePrimes (N : ℕ) (hN : 3 ≤ N) :
    widePrimes N ⊆ largePrimes N := by
  intro p hp
  obtain ⟨hp4, hpnot⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hpbound, hpprime⟩ := Nat.mem_primesLE.mp hp4
  have hNp : N < p := by
    by_contra h
    exact hpnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
  have hsq : 4 < N ^ 2 := by nlinarith
  have hbound : 4 * N < N ^ 3 := by
    have := Nat.mul_lt_mul_of_pos_right hsq (show 0 < N by omega)
    simpa only [pow_succ] using this
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_primesBelow.mpr ⟨hpbound.trans_lt hbound, hpprime⟩, hNp⟩

/-- The explicit prime reserve yields a pure integer-power cardinal bound. -/
theorem pow_thirtysix_le_twentyfour_squareD_card
    (M : ℕ) (hM : 262144 ≤ M) :
    M ^ 36 ≤ 24 * (squareD (M ^ 10)).card := by
  have hN : 3 ≤ M ^ 10 := by
    have hself : M ≤ M ^ 10 := le_self_pow₀ (by omega) (by decide : (10 : ℕ) ≠ 0)
    omega
  have hreserve : 4 * M ^ 9 ≤ (widePrimes (M ^ 10)).card :=
    widePrimes_card_pure_power M (M ^ 10) hM le_rfl (by nlinarith)
  have hR : 1 ≤ M ^ 9 := one_le_pow₀ (by omega)
  have h := pow_four_le_twentyfour_squareD_card (M ^ 10) (by omega)
    (widePrimes (M ^ 10)) (widePrimes_subset_largePrimes _ hN) (M ^ 9) hR hreserve
  simpa only [← pow_mul] using h

end ReciprocalSquares
