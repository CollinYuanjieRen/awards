import Jsp285.OccurrenceNet
import Jsp285.OccurrenceResidues
import Jsp285.OccurrenceTransport

namespace Jsp285

open scoped BigOperators Pointwise

/-- Occurrence-indexed form of the Szemerédi--Vu endgame: a fixed-step source
and a positive, eventually linearly bounded residue source combine to contain
an infinite arithmetic progression. -/
theorem fixedStep_and_occurrence_residue_part
    (b r : ℕ → ℕ) (hrpos : ∀ i, 0 < r i) (D : ℕ) (hD : 2 ≤ D)
    (hrbound : ∃ I₀, ∀ i, I₀ ≤ i → r i ≤ i / D)
    (hfixed : Erdos344.HasFixedStepProgressions
      (indexedSubsetSums b Set.univ)) :
    Erdos344.ContainsInfiniteAP
      (indexedSubsetSums b Set.univ + indexedSubsetSums r Set.univ) := by
  obtain ⟨d, hd, hlong⟩ := hfixed
  obtain ⟨q, hqpos, hqd, s, htailq, hresmod⟩ :=
    exists_occurrence_residue_stabilization r hd
  let y : ℕ → ℕ := fun j => r (s + j)
  have hypos : ∀ j, 0 < y j := fun j => hrpos (s + j)
  have hyq : ∀ j, q ∣ y j := by
    intro j
    exact htailq (s + j) (Nat.le_add_right s j)
  obtain ⟨I₀, hI₀⟩ := hrbound
  have hygrowth : ∃ m₀, ∀ j, m₀ ≤ j → y j ≤ occurrencePrefixSum y j := by
    refine ⟨max I₀ s, ?_⟩
    intro j hj
    have hI₀j : I₀ ≤ s + j :=
      (le_max_left I₀ s).trans hj |>.trans (Nat.le_add_left j s)
    have hsj : s ≤ j := (le_max_right I₀ s).trans hj
    have hsumle : s + j ≤ D * j := by
      calc
        s + j ≤ j + j := Nat.add_le_add_right hsj j
        _ = 2 * j := by omega
        _ ≤ D * j := Nat.mul_le_mul_right j hD
    have hyj : y j ≤ j :=
      (hI₀ (s + j) hI₀j).trans (Nat.div_le_of_le_mul hsumle)
    calc
      y j ≤ j := hyj
      _ = ∑ _i ∈ Finset.range j, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range j, y i := by
        exact Finset.sum_le_sum fun i _ => hypos i
      _ = occurrencePrefixSum y j := rfl
  obtain ⟨K, hnet⟩ :=
    exists_addNet_indexedSubsetSums hqpos y hypos hyq hygrowth
  let M := d / q
  have hqle : q ≤ d := Nat.le_of_dvd hd hqd
  have hMpos : 0 < M := Nat.div_pos hqle hqpos
  have hdEq : q * M = d := Nat.mul_div_cancel' hqd
  let P := occurrenceSums r (Finset.range s)
  let Z := ∑ i ∈ Finset.range s, r i
  let L := Z + (K + 1)
  obtain ⟨a, ha⟩ := hlong L
  have hAP : ∀ j < L,
      a + j * (q * M) ∈ indexedSubsetSums b Set.univ := by
    simpa [hdEq] using ha
  have hres : ∀ i < M, ∃ u ∈ (P : Set ℕ),
      ∃ z ≤ Z, u = i * q + (q * M) * z := by
    intro i hi
    obtain ⟨u, huP, hucong⟩ := hresmod i (by simpa [M] using hi)
    have hiqd : i * q < d := by
      rw [← hdEq]
      nlinarith
    have hucong' : (u : ZMod d) = (i * q : ℕ) := by
      simpa only [Nat.cast_mul] using hucong
    obtain ⟨z, huz⟩ :=
      Erdos344.exists_eq_add_mul_of_zmod_eq hd hiqd hucong'
    have hz : z ≤ Z := by
      have hzu : z ≤ u := by
        have hdz : z ≤ d * z := Nat.le_mul_of_pos_left z hd
        omega
      exact hzu.trans (occurrenceSum_le_mass huP)
    exact ⟨u, huP, z, hz, by simpa [hdEq, mul_comm] using huz⟩
  have hlength : K + 1 ≤ M * (L - Z) := by
    have : L - Z = K + 1 := by simp [L]
    rw [this]
    nlinarith
  have hlowered : ∀ n < M * (L - Z),
      (a + (q * M) * Z) + n * q ∈
        indexedSubsetSums b Set.univ + (P : Set ℕ) :=
    Erdos344.lowerStep_of_residue_translates_mem hqpos hMpos hAP hres
  have hfinite : ∀ n < K + 1,
      (a + (q * M) * Z) + n * q ∈
        indexedSubsetSums b Set.univ + (P : Set ℕ) :=
    fun n hn => hlowered n (hn.trans_le hlength)
  have hinf := Erdos344.addNet_add_finiteAP hnet hfinite
  apply Erdos344.containsInfiniteAP_mono ?_ hinf
  rintro x ⟨bp, hbp, t, ht, rfl⟩
  obtain ⟨bv, hb, p, hp, rfl⟩ := hbp
  have hp' : p ∈ indexedSubsetSums r (Set.Iio s) :=
    occurrenceSums_range_subset_indexedSubsetSums_Iio r s hp
  have ht' : t ∈ indexedSubsetSums r (Set.Ici s) := by
    exact indexedSubsetSums_tail_subset r s ht
  have hpt : p + t ∈ indexedSubsetSums r Set.univ := by
    have hdisj : Disjoint (Set.Iio s) (Set.Ici s) :=
      Set.Iio_disjoint_Ici le_rfl
    have hadd := add_mem_indexedSubsetSums r hdisj hp' ht'
    simpa only [Set.Iio_union_Ici] using hadd
  exact ⟨bv, hb, p + t, hpt, by ring⟩

end Jsp285
