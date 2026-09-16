import Jsp285.OccurrenceModular

/-! Adding distinct pivot occurrences with repeated weights. -/

namespace Jsp285

open scoped BigOperators

/-- Adjoining a fresh occurrence contains both the old subset sums and their
translate by the weight of that occurrence. -/
lemma union_natAddTranslate_occurrenceSums_subset
    {ι : Type*} [DecidableEq ι] (v : ι → ℕ) (I : Finset ι) (i : ι)
    (hi : i ∉ I) :
    occurrenceSums v I ∪ Erdos344.natAddTranslate (v i) (occurrenceSums v I) ⊆
      occurrenceSums v (insert i I) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact occurrenceSums_mono v (Finset.subset_insert i I) hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨J, hJI, rfl⟩ := mem_occurrenceSums.mp hy
    apply mem_occurrenceSums.mpr
    refine ⟨insert i J, Finset.insert_subset_insert i hJI, ?_⟩
    rw [Finset.sum_insert (fun hij => hi (hJI hij))]
    omega

/-- Adding distinct positive pivot occurrences grows the occurrence subset-sum
set by at least the sum of their weights, provided the base sums cover every
residue modulo each pivot weight. -/
theorem card_occurrenceSums_add_pivots
    {ι : Type*} [DecidableEq ι] (v : ι → ℕ) (B P : Finset ι)
    (hdisj : Disjoint B P) (hpos : ∀ i ∈ P, 0 < v i)
    (hcover : ∀ i ∈ P, ∀ z : ZMod (v i),
      ∃ x ∈ occurrenceSums v B, (x : ZMod (v i)) = z) :
    (occurrenceSums v B).card + ∑ i ∈ P, v i ≤
      (occurrenceSums v (B ∪ P)).card := by
  classical
  induction P using Finset.induction with
  | empty => simp
  | @insert i P hiP ih =>
      have hiB : i ∉ B := by
        intro hi
        exact Finset.disjoint_left.mp hdisj hi
          (Finset.mem_insert_self i P)
      have hdisjP : Disjoint B P :=
        hdisj.mono_right (Finset.subset_insert i P)
      have hposP : ∀ j ∈ P, 0 < v j := by
        intro j hj
        exact hpos j (Finset.mem_insert_of_mem hj)
      have hcoverP : ∀ j ∈ P, ∀ z : ZMod (v j),
          ∃ x ∈ occurrenceSums v B, (x : ZMod (v j)) = z := by
        intro j hj
        exact hcover j (Finset.mem_insert_of_mem hj)
      have hIH := ih hdisjP hposP hcoverP
      have hvi : 0 < v i := hpos i (Finset.mem_insert_self i P)
      let _ : NeZero (v i) := ⟨hvi.ne'⟩
      let T := occurrenceSums v (B ∪ P)
      have hbase : occurrenceSums v B ⊆ T :=
        occurrenceSums_mono v (Finset.subset_union_left)
      have hres :
          (T.image fun x : ℕ => (x : ZMod (v i))).card = v i := by
        have himage : T.image (fun x : ℕ => (x : ZMod (v i))) = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro z
          obtain ⟨x, hx, hxz⟩ := hcover i (Finset.mem_insert_self i P) z
          exact Finset.mem_image.mpr ⟨x, hbase hx, hxz⟩
        rw [himage, Finset.card_univ, ZMod.card]
      have hgrowth := Erdos344.card_add_modulus_growth hvi T
      have hiBP : i ∉ B ∪ P := by simp [hiB, hiP]
      have hsubset :
          T ∪ Erdos344.natAddTranslate (v i) T ⊆
            occurrenceSums v (insert i (B ∪ P)) :=
        union_natAddTranslate_occurrenceSums_subset v (B ∪ P) i hiBP
      rw [Finset.sum_insert hiP, Finset.union_insert]
      calc
        (occurrenceSums v B).card + (v i + ∑ j ∈ P, v j) =
            ((occurrenceSums v B).card + ∑ j ∈ P, v j) + v i := by omega
        _ ≤ T.card + v i := Nat.add_le_add_right hIH _
        _ = T.card + (T.image fun x : ℕ => (x : ZMod (v i))).card := by
          rw [hres]
        _ ≤ (T ∪ Erdos344.natAddTranslate (v i) T).card := hgrowth
        _ ≤ (occurrenceSums v (insert i (B ∪ P))).card :=
          Finset.card_le_card hsubset

end Jsp285
