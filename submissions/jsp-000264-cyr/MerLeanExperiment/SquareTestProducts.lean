import MerLeanExperiment.SquareSubproducts
import MerLeanExperiment.SquareModulus

namespace ReciprocalSquares

/-- A smooth-square factor times a nonempty large-prime subproduct survives erasure. -/
theorem squareB_mul_subproduct_mem_squareD (N b : ℕ)
    (hb : b ∈ squareB N) (S : Finset ℕ)
    (hS : S ⊆ largePrimes N) (hne : S.Nonempty) :
    b * (S.prod id) ^ 2 ∈ squareD N := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨a * S.prod id, ?_, by simp only [mul_pow]⟩
    apply Finset.mem_image.mpr
    exact ⟨(a, S), Finset.mem_product.mpr ⟨ha, Finset.mem_powerset.mpr hS⟩, rfl⟩
  · intro he
    obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp he
    have hroot : c = a * S.prod id :=
      Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) (by simpa only [mul_pow] using heq)
    have hsmooth : c ∈ Nat.smoothNumbers (N + 1) := (Finset.mem_filter.mp hc).2
    obtain ⟨p, hp⟩ := hne
    have hpprime := largePrimes_prime (hS hp)
    have hpdiv : p ∣ c := by
      rw [hroot]
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hp) a
    have hsmall := Nat.mem_smoothNumbers'.mp hsmooth p hpprime hpdiv
    have hlarge : N < p := (Finset.mem_filter.mp (hS hp)).2
    omega

/-- An additional large prime outside the subset gives a retained pure subproduct. -/
theorem square_prime_mul_subproduct_mem_squareD (N : ℕ) (hN : 2 ≤ N)
    (p : ℕ) (hp : p ∈ largePrimes N) (S : Finset ℕ)
    (hS : S ⊆ largePrimes N) (hpnot : p ∉ S) :
    p ^ 2 * (S.prod id) ^ 2 ∈ squareD N := by
  have hsub : insert p S ⊆ largePrimes N := Finset.insert_subset hp hS
  have hmem := square_subproduct_mem_squareD N hN (insert p S) hsub
    (Finset.insert_nonempty _ _)
  simpa only [Finset.prod_insert hpnot, id_eq, mul_pow] using hmem

/-- Both kinds of factors used to construct square denominators are positive. -/
theorem square_factor_pos {N b : ℕ} (hb : b ∈ squareB N ∪ squareQ N) : 0 < b := by
  rcases Finset.mem_union.mp hb with hb | hb
  · exact (squareB_bounds hb).1
  · exact (squareQ_bounds hb).1

/-- A missing factor automatically lies outside the prime support when it is a prime square. -/
theorem square_test_product_mem_squareD (N : ℕ) (hN : 2 ≤ N)
    (b : ℕ) (hb : b ∈ squareB N ∪ squareQ N)
    (G : Finset ℕ) (hG : G ⊆ largePrimes N)
    (M : ℤ) (hdiv : ∀ p ∈ G, ((p ^ 2 : ℕ) : ℤ) ∣ M)
    (hmissing : ¬ (b : ℤ) ∣ M)
    (S : Finset ℕ) (hS : S ⊆ G) (hne : S.Nonempty) :
    b * (S.prod id) ^ 2 ∈ squareD N := by
  rcases Finset.mem_union.mp hb with hb | hb
  · exact squareB_mul_subproduct_mem_squareD N b hb S (hS.trans hG) hne
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    have hpnot : p ∉ G := fun hpg => hmissing (hdiv p hpg)
    exact square_prime_mul_subproduct_mem_squareD N hN p hp S (hS.trans hG)
      (fun hps => hpnot (hS hps))

/-- Multiplication by a fixed positive construction factor preserves subset-product injectivity. -/
theorem square_test_product_injOn (N : ℕ) (hN : 2 ≤ N)
    (b : ℕ) (hb : b ∈ squareB N ∪ squareQ N)
    (G : Finset ℕ) (hG : G ⊆ largePrimes N) :
    Set.InjOn (fun S : Finset ℕ => b * (S.prod id) ^ 2)
      (↑G.powerset : Set (Finset ℕ)) := by
  intro S hS T hT heq
  have hsq : (S.prod id) ^ 2 = (T.prod id) ^ 2 :=
    Nat.mul_left_cancel (square_factor_pos hb) heq
  exact square_subproduct_injOn N hN
    (Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hS).trans hG))
    (Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hT).trans hG)) hsq

/-- Test denominators with a fixed factor and a fixed number of large prime factors. -/
def squareTestProducts (b : ℕ) (G : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (G.powersetCard k).image (fun S => b * (S.prod id) ^ 2)

theorem squareTestProducts_card (N : ℕ) (hN : 2 ≤ N)
    (b : ℕ) (hb : b ∈ squareB N ∪ squareQ N)
    (G : Finset ℕ) (hG : G ⊆ largePrimes N) (k : ℕ) :
    (squareTestProducts b G k).card = G.card.choose k := by
  rw [squareTestProducts, Finset.card_image_of_injOn, Finset.card_powersetCard]
  intro S hS T hT heq
  exact square_test_product_injOn N hN b hb G hG
    (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hS).1)
    (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1) heq

theorem squareTestProducts_subset_squareD (N : ℕ) (hN : 2 ≤ N)
    (b : ℕ) (hb : b ∈ squareB N ∪ squareQ N)
    (G : Finset ℕ) (hG : G ⊆ largePrimes N)
    (M : ℤ) (hdiv : ∀ p ∈ G, ((p ^ 2 : ℕ) : ℤ) ∣ M)
    (hmissing : ¬ (b : ℤ) ∣ M) (k : ℕ) (hk : 1 ≤ k) :
    squareTestProducts b G k ⊆ squareD N := by
  intro d hd
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  exact square_test_product_mem_squareD N hN b hb G hG M hdiv hmissing S hsub
    (Finset.card_pos.mp (by omega))

end ReciprocalSquares
