import MerLeanExperiment.DenseExtensions
import MerLeanExperiment.SquareConstruction
import MerLeanExperiment.CoherentMultiples

namespace ReciprocalSquares

/-- Twenty-element prime subsets whose square product has a nearby integer multiple. -/
noncomputable def goodPrimeSubsets (N : ℕ) (h : ℤ) (T : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact (T.powersetCard 20).filter fun S => ∃ M : ℤ,
    (((S.prod id) ^ 2 : ℕ) : ℤ) ∣ M ∧ |h - M| ≤ (N ^ 36 : ℕ)

/-- A nineteen-prime prefix has square product larger than twice the search radius. -/
theorem prime_prefix_square_separation (N : ℕ) (hN : 2 ≤ N)
    (A : Finset ℕ) (hA : A ⊆ largePrimes N) (hcard : A.card = 19) :
    2 * N ^ 36 < (A.prod id) ^ 2 := by
  have hprod : N ^ 19 ≤ A.prod id := by
    calc
      N ^ 19 = ∏ _p ∈ A, N := by simp [hcard]
      _ ≤ A.prod id := Finset.prod_le_prod' (fun p hp =>
        (Finset.mem_filter.mp (hA hp)).2.le)
  have hlarge : N ^ 38 ≤ (A.prod id) ^ 2 := by
    calc
      N ^ 38 = (N ^ 19) ^ 2 := by ring
      _ ≤ (A.prod id) ^ 2 := Nat.pow_le_pow_left hprod 2
  have hsq : 2 < N ^ 2 := by nlinarith
  have hNpos : 0 < N := by omega
  calc
    2 * N ^ 36 < N ^ 2 * N ^ 36 :=
      Nat.mul_lt_mul_of_pos_right hsq (pow_pos hNpos _)
    _ = N ^ 38 := by ring
    _ ≤ (A.prod id) ^ 2 := hlarge

/-- A dense family of good twenty-prime subsets yields many prime squares
which divide one common nearby integer. -/
theorem exists_large_coherent_prime_subset
    (N R : ℕ) (h : ℤ) (T : Finset ℕ)
    (hN : 2 ≤ N) (hR : 15 ≤ R) (hT : T ⊆ largePrimes N)
    (hcard : 4 * R ≤ T.card)
    (hdensity : 3 * (T.powersetCard 20).card ≤ 4 * (goodPrimeSubsets N h T).card) :
    ∃ G : Finset ℕ, G ⊆ T ∧ 2 * R ≤ G.card ∧
      ∃ M : ℤ, |h - M| ≤ (N ^ 36 : ℕ) ∧
        ∀ p ∈ G, ((p ^ 2 : ℕ) : ℤ) ∣ M := by
  classical
  have hr : 19 < T.card := by omega
  have hfamily : goodPrimeSubsets N h T ⊆ T.powersetCard (19 + 1) := by
    unfold goodPrimeSubsets
    exact Finset.filter_subset _ _
  obtain ⟨A, hA, hdegree⟩ := exists_dense_extensions T (goodPrimeSubsets N h T)
    19 3 4 hr hfamily hdensity
  obtain ⟨hAT, hAcard⟩ := Finset.mem_powersetCard.mp hA
  let G := extensions T (goodPrimeSubsets N h T) A
  have hGT : G ⊆ T := by
    intro p hp
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have hGcard : 2 * R ≤ G.card := by
    change 3 * (T.card - 19) ≤ 4 * G.card at hdegree
    omega
  have hGne : G.Nonempty := Finset.card_pos.mp (by omega)
  let P : ℤ := (((A.prod id) ^ 2 : ℕ) : ℤ)
  have hsep : 2 * (N ^ 36 : ℕ) < P := by
    dsimp [P]
    exact_mod_cast prime_prefix_square_separation N hN A (hAT.trans hT) hAcard
  let Q := G.image (fun p => p ^ 2)
  have hQne : Q.Nonempty := hGne.image _
  have hnear : ∀ q ∈ Q, ∃ M : ℤ,
      P * (q : ℤ) ∣ M ∧ |h - M| ≤ (N ^ 36 : ℕ) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hpnot : p ∉ A := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).2
    have hgood : insert p A ∈ goodPrimeSubsets N h T := (Finset.mem_filter.mp hp).2
    obtain ⟨M, hdiv, hclose⟩ := (Finset.mem_filter.mp hgood).2
    refine ⟨M, ?_, hclose⟩
    simpa only [P, Finset.prod_insert hpnot, id_eq, mul_pow, Nat.cast_mul, mul_comm] using hdiv
  obtain ⟨M, hPM, hclose, hdiv⟩ := exists_common_near_multiple P (N ^ 36 : ℕ) h Q hQne hsep hnear
  refine ⟨G, hGT, hGcard, M, hclose, ?_⟩
  intro p hp
  exact hdiv (p ^ 2) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

end ReciprocalSquares
