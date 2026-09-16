import MerLeanExperiment.SquareConstruction
import MerLeanExperiment.LcmSupport

namespace ReciprocalSquares

open scoped BigOperators

/-- The finite Fourier modulus of the retained square denominators. -/
def squareModulus (N : ℕ) : ℕ := (squareD N).lcm id

theorem squareB_card_le (N : ℕ) : (squareB N).card ≤ N ^ 3 := by
  calc
    (squareB N).card ≤ (smoothRoots N).card := Finset.card_image_le
    _ ≤ (Finset.range (N ^ 3)).card := Finset.card_filter_le _ _
    _ = N ^ 3 := Finset.card_range _

theorem squareQ_card_le (N : ℕ) : (squareQ N).card ≤ N ^ 3 := by
  calc
    (squareQ N).card ≤ (largePrimes N).card := Finset.card_image_le
    _ ≤ (Nat.primesBelow (N ^ 3)).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range (N ^ 3)).card := Finset.card_le_card (by
      intro p hp
      exact Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1)
    _ = N ^ 3 := Finset.card_range _

theorem squareB_bounds {N b : ℕ} (hb : b ∈ squareB N) :
    0 < b ∧ b ≤ N ^ 6 := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have hapos : 0 < a := Nat.pos_of_ne_zero
    (Nat.ne_zero_of_mem_smoothNumbers (Finset.mem_filter.mp ha).2)
  have hbound : a < N ^ 3 := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  refine ⟨pow_pos hapos _, ?_⟩
  calc
    a ^ 2 ≤ (N ^ 3) ^ 2 := Nat.pow_le_pow_left hbound.le 2
    _ = N ^ 6 := by ring

theorem squareQ_bounds {N q : ℕ} (hq : q ∈ squareQ N) :
    0 < q ∧ q ≤ N ^ 6 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hpprime := largePrimes_prime hp
  have hbound : p < N ^ 3 :=
    (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).1
  refine ⟨pow_pos hpprime.pos _, ?_⟩
  calc
    p ^ 2 ≤ (N ^ 3) ^ 2 := Nat.pow_le_pow_left hbound.le 2
    _ = N ^ 6 := by ring

/-- The full prime-square product covers any subset product. -/
theorem squareZ_dvd_product {N d : ℕ} (hd : d ∈ squareZ N) :
    d ∣ (squareB N).prod id * (squareQ N).prod id := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨⟨b, S⟩, hpair, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hb, hS⟩ := Finset.mem_product.mp hpair
  have hsub : S ⊆ largePrimes N := Finset.mem_powerset.mp hS
  have hbdiv : b ^ 2 ∣ (squareB N).prod id :=
    Finset.dvd_prod_of_mem id (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  have hQprod : (squareQ N).prod id = ((largePrimes N).prod id) ^ 2 := by
    rw [squareQ, Finset.prod_image]
    · exact Finset.prod_pow _ _ _
    · intro x hx y hy hxy
      dsimp at hxy
      nlinarith
  have hSdiv : S.prod id ∣ (largePrimes N).prod id :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hSsq : (S.prod id) ^ 2 ∣ (squareQ N).prod id := by
    rw [hQprod]
    exact pow_dvd_pow_of_dvd hSdiv 2
  simpa only [rootProduct, mul_pow] using Nat.mul_dvd_mul hbdiv hSsq

theorem squareModulus_dvd_product (N : ℕ) :
    squareModulus N ∣ (squareB N).prod id * (squareQ N).prod id := by
  apply Finset.lcm_dvd
  intro d hd
  exact squareZ_dvd_product (Finset.mem_sdiff.mp hd).1

theorem squareModulus_pos (N : ℕ) : 0 < squareModulus N := by
  apply finset_lcm_pos
  intro d hd
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hd).1
  exact pow_pos (rootsZ_pos ha) _

/-- A finite product bound for the actual constructed modulus. -/
theorem squareModulus_le (N : ℕ) (hN : 2 ≤ N) :
    squareModulus N ≤ (N ^ 6) ^ (2 * N ^ 3) := by
  have hbase : 1 ≤ N ^ 6 := Nat.one_le_pow 6 N (by omega)
  have hBpos : 0 < (squareB N).prod id :=
    Finset.prod_pos (fun b hb => (squareB_bounds hb).1)
  have hQpos : 0 < (squareQ N).prod id :=
    Finset.prod_pos (fun q hq => (squareQ_bounds hq).1)
  have hB : (squareB N).prod id ≤ (N ^ 6) ^ (N ^ 3) := by
    calc
      (squareB N).prod id ≤ (N ^ 6) ^ (squareB N).card :=
        Finset.prod_le_pow_card _ _ _ (fun b hb => (squareB_bounds hb).2)
      _ ≤ (N ^ 6) ^ (N ^ 3) := pow_le_pow_right₀ hbase (squareB_card_le N)
  have hQ : (squareQ N).prod id ≤ (N ^ 6) ^ (N ^ 3) := by
    calc
      (squareQ N).prod id ≤ (N ^ 6) ^ (squareQ N).card :=
        Finset.prod_le_pow_card _ _ _ (fun q hq => (squareQ_bounds hq).2)
      _ ≤ (N ^ 6) ^ (N ^ 3) := pow_le_pow_right₀ hbase (squareQ_card_le N)
  calc
    squareModulus N ≤ (squareB N).prod id * (squareQ N).prod id :=
      Nat.le_of_dvd (Nat.mul_pos hBpos hQpos) (squareModulus_dvd_product N)
    _ ≤ (N ^ 6) ^ (N ^ 3) * (N ^ 6) ^ (N ^ 3) := Nat.mul_le_mul hB hQ
    _ = (N ^ 6) ^ (2 * N ^ 3) := by rw [← pow_add]; congr 1; omega

/-- The logarithmic size estimate used to count high frequencies. -/
theorem squareModulus_log_le (N : ℕ) (hN : 2 ≤ N) :
    Real.log (squareModulus N : ℝ) ≤
      12 * (N : ℝ) ^ 3 * Real.log (N : ℝ) := by
  have hmpos : (0 : ℝ) < squareModulus N := by exact_mod_cast squareModulus_pos N
  have hmle : (squareModulus N : ℝ) ≤ ((N : ℝ) ^ 6) ^ (2 * N ^ 3) := by
    exact_mod_cast squareModulus_le N hN
  calc
    Real.log (squareModulus N : ℝ) ≤ Real.log (((N : ℝ) ^ 6) ^ (2 * N ^ 3)) :=
      Real.log_le_log hmpos hmle
    _ = 12 * (N : ℝ) ^ 3 * Real.log (N : ℝ) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast
      ring

end ReciprocalSquares
