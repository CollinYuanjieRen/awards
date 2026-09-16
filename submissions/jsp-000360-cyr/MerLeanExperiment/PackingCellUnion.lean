import MerLeanExperiment.PackingCellDefinitions
import MerLeanExperiment.TranslationUnion
import MerLeanExperiment.CellCover

namespace Erdos441

theorem packing_cell_union_bound {K : ℕ} (M N : ℕ) (hM : 2 ≤ M)
    (hN : 0 < N) (r ell : Fin K → ℤ) (hr : Function.Injective r)
    (hsize : ∀ i j, i ≠ j → 2 * (r j - r i).natAbs ≤ M)
    (c E : Fin K → ℝ) (hc : ∀ i, 0 < c i) (hE : ∀ i, 0 ≤ E i)
    (delta B : ℝ) (hdelta : 0 ≤ delta) (hB : ∀ i, c i + delta ≤ B)
    (hpoint : ∀ i, c i * Real.sqrt (N : ℝ) < (shiftedPoint M r ell i : ℝ) ∧
      (shiftedPoint M r ell i : ℝ) ≤ c i * Real.sqrt (N : ℝ) + E i)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤
      (shiftParityWeight (r i) (r j) : ℝ) * c i * c j)
    (A : Finset ℕ) (hA : LcmBounded N A) :
    ((packingCellUnion A r c delta (Real.sqrt (N : ℝ))).card : ℝ) ≤
      delta * Real.sqrt (N : ℝ) / 2 + (∑ i, (E i + 1)) +
        ((packingBadPoints A (shiftProductNat M r ell) B (Real.sqrt (N : ℝ))).card : ℝ) := by
  classical
  let R : ℝ := Real.sqrt (N : ℝ)
  let D := shiftProductNat M r ell
  let H : ℤ := ⌊delta * R / 2⌋
  let S : Fin K → Finset ℕ := fun i =>
    (realIntIoc (c i * R) (c i * R + E i)).image Int.natAbs
  let U := Finset.univ.biUnion S
  let G := goodTranslateUnion A D (shiftedPoint M r ell) H
  let Bad := packingBadPoints A D B R
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hfact : Even (M.factorial : ℤ) := by
    apply even_iff_two_dvd.mpr
    exact_mod_cast Nat.dvd_factorial (by omega : 0 < 2) hM
  have hcover : packingCellUnion A r c delta R ⊆ (G ∪ U) ∪ Bad := by
    intro n hn
    obtain ⟨i, _, hni⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hnA, hnlo, hnhi, hnpar⟩ := Finset.mem_filter.mp hni
    by_cases hcop : Nat.Coprime n D
    · have hpar : Even ((n : ℤ) - shiftedPoint M r ell i) := by
        have heq : (n : ℤ) - shiftedPoint M r ell i =
            ((n : ℤ) - r i) - (M.factorial : ℤ) * ell i := by
          unfold shiftedPoint
          ring
        rw [heq]
        exact hnpar.sub (hfact.mul_right (ell i))
      have hnloR : c i * R < ((n : ℤ) : ℝ) := by exact_mod_cast hnlo
      have hnhiR : ((n : ℤ) : ℝ) ≤ (c i + delta) * R := by exact_mod_cast hnhi
      rcases cell_point_cover (c i) delta R (E i) (shiftedPoint M r ell i) (n : ℤ)
          (hpoint i).1 (hpoint i).2 hnloR hnhiR hpar with hshort | ⟨h, hh, heq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        exact Finset.mem_image.mpr ⟨(n : ℤ), hshort, by simp⟩
      · have hnabs : (shiftedPoint M r ell i + 2 * h).natAbs = n := by rw [← heq]; simp
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨h, hh, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨i, ?_, hnabs⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnabs]
        exact ⟨hnA, hcop⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨hnA, hnhi.trans (mul_le_mul_of_nonneg_right (hB i) hR), hcop⟩
  have hGnat : G.card ≤ H.toNat :=
    translated_good_union_card M N hM hN r ell hr hsize c hc
      (fun i => (hpoint i).1) hsep A hA H
  have hHnonneg : 0 ≤ H := Int.floor_nonneg.mpr (by positivity)
  have hH : (H.toNat : ℝ) ≤ delta * R / 2 := by
    have he : (H.toNat : ℝ) = (H : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hHnonneg
    rw [he]
    exact Int.floor_le _
  have hG : (G.card : ℝ) ≤ delta * R / 2 := (Nat.cast_le.mpr hGnat).trans hH
  have hU : (U.card : ℝ) ≤ ∑ i, (E i + 1) := by
    have hUnat : U.card ≤ ∑ i, (S i).card := Finset.card_biUnion_le
    calc
      _ ≤ ∑ i, ((S i).card : ℝ) := by exact_mod_cast hUnat
      _ ≤ ∑ i, (E i + 1) := by
        apply Finset.sum_le_sum
        intro i _
        have himg : (S i).card ≤ (realIntIoc (c i * R) (c i * R + E i)).card :=
          Finset.card_image_le
        have hcount := card_realIntIoc_le (c i * R) (c i * R + E i) (by linarith [hE i])
        exact (Nat.cast_le.mpr himg).trans (by linarith)
  have hcardNat : (packingCellUnion A r c delta R).card ≤ G.card + U.card + Bad.card :=
    (Finset.card_le_card hcover).trans
      ((Finset.card_union_le (G ∪ U) Bad).trans
        (Nat.add_le_add_right (Finset.card_union_le G U) _))
  have hcard : ((packingCellUnion A r c delta R).card : ℝ) ≤
      (G.card : ℝ) + U.card + Bad.card := by exact_mod_cast hcardNat
  change ((packingCellUnion A r c delta R).card : ℝ) ≤
    delta * R / 2 + (∑ i, (E i + 1)) + (Bad.card : ℝ)
  linarith

end Erdos441

#print axioms Erdos441.packing_cell_union_bound
