import MerLeanExperiment.FiberAverage
import MerLeanExperiment.SelectedMeshCells
import MerLeanExperiment.ParityGroups
import Mathlib.Tactic

namespace Erdos441

open scoped BigOperators

/-- Choose one distinct mesh cell for every label inside each owner/parity
fiber.  Fiberwise averaging then bounds the actual union of the selected
packing cells. -/
theorem exists_averaged_mesh {K l : ℕ} (A : Finset ℕ) (a b : Fin l → ℝ)
    (o : Fin K → Fin l) (r : Fin K → ℤ) (m : Fin l → ℕ) (delta R : ℝ)
    (hd : 0 < delta) (hR : 0 < R) (hm : ∀ j, 0 < m j)
    (hKm : ∀ j, K ≤ m j)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) :
    ∃ c : Fin K → ℝ,
      (∀ i, a (o i) ≤ c i ∧ c i + delta ≤ b (o i)) ∧
      (∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))) ≤
        (packingCellUnion A r c delta R).card := by
  classical
  let Fiber := fun g : Fin l × Bool ↦ {i : Fin K // ownerParity o r i = g}
  have hfiberK (g : Fin l × Bool) : Fintype.card (Fiber g) ≤ K := by
    simpa [Fiber] using
      Fintype.card_le_of_injective (fun i : Fiber g ↦ i.val) Subtype.val_injective
  have havg (g : Fin l × Bool) :
      ∃ sg : Fiber g → Fin (m g.1), Function.Injective sg ∧
        (Fintype.card (Fiber g) : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ)) ≤
          ∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg i).val).card : ℝ) := by
    exact exists_injective_average (I := Fiber g) (m g.1) (hm g.1)
      ((hfiberK g).trans (hKm g.1))
      (fun s : Fin (m g.1) ↦
        ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))
  choose sg hsg_inj hsg_avg using havg
  have hsg_transport (g h : Fin l × Bool) (e : g = h) (i : Fiber g) :
      (sg g i).val = (sg h ⟨i.val, i.property.trans e⟩).val := by
    subst h
    rfl
  let sigma : ∀ i : Fin K, Fin (m (o i)) := fun i ↦
    sg (ownerParity o r i) ⟨i, rfl⟩
  let c : Fin K → ℝ := fun i ↦ a (o i) + (sigma i).val * delta
  refine ⟨c, ?_, ?_⟩
  · simpa [c] using selected_mesh_bounds a b o m sigma delta hd.le hmesh
  · have hsigma_inj : ∀ i j, ownerParity o r i = ownerParity o r j →
        (sigma i).val = (sigma j).val → i = j := by
      intro i j hg hsval
      let ii : Fiber (ownerParity o r i) := ⟨i, rfl⟩
      let jj : Fiber (ownerParity o r j) := ⟨j, rfl⟩
      let jj' : Fiber (ownerParity o r i) := ⟨j, hg.symm⟩
      have hsval' : (sg (ownerParity o r i) ii).val =
          (sg (ownerParity o r j) jj).val := by
        exact hsval
      have htrans : (sg (ownerParity o r j) jj).val =
          (sg (ownerParity o r i) jj').val := by
        simpa [jj, jj'] using
          hsg_transport (ownerParity o r j) (ownerParity o r i) hg.symm jj
      have hsfin : sg (ownerParity o r i) ii =
          sg (ownerParity o r i) jj' := by
        apply Fin.ext
        exact hsval'.trans htrans
      exact congrArg Subtype.val (hsg_inj (ownerParity o r i) hsfin)
    have hcardN := selected_mesh_cells_card A a b o r m sigma delta R hd hR
      hmesh hdisj hsigma_inj
    have hcardR : ((packingCellUnion A r c delta R).card : ℝ) =
        ∑ i : Fin K, ((packingCell A r c delta R i).card : ℝ) := by
      dsimp [c]
      exact_mod_cast hcardN
    have hcell (i : Fin K) :
        packingCell A r c delta R i =
          consecutiveCell A (a (o i)) delta R
            (parityRep (ownerParity o r i).2) (sigma i).val := by
      ext n
      simp only [packingCell, consecutiveCell, parityRegion, Finset.mem_filter]
      rw [even_sub_parity_rep (n : ℤ) (r i)]
      simp only [ownerParity]
      dsimp [c]
      constructor
      · rintro ⟨hnA, hnlo, hnhi, hnpar⟩
        refine ⟨hnA, hnlo, ?_, hnpar⟩
        convert hnhi using 1 <;> ring
      · rintro ⟨hnA, hnlo, hnhi, hnpar⟩
        refine ⟨hnA, hnlo, ?_, hnpar⟩
        convert hnhi using 1 <;> ring
    have hfiber_eq (g : Fin l × Bool) :
        (∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg g i).val).card : ℝ)) =
          ∑ i : Fiber g, ((packingCell A r c delta R i.val).card : ℝ) := by
      apply Fintype.sum_congr
      intro i
      rw [hcell i.val]
      have ho : o i.val = g.1 := congrArg Prod.fst i.property
      have hv : (ownerParity o r i.val).2 = g.2 := congrArg Prod.snd i.property
      have hs : (sigma i.val).val = (sg g i).val := by
        dsimp [sigma]
        simpa using hsg_transport (ownerParity o r i.val) g i.property
          (⟨i.val, rfl⟩ : Fiber (ownerParity o r i.val))
      have ha : a (o i.val) = a g.1 := congrArg a ho
      have hr : parityRep (ownerParity o r i.val).2 = parityRep g.2 :=
        congrArg parityRep hv
      rw [ha, hr, hs]
    calc
      (∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 *
            (∑ s : Fin (m g.1),
              ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ))) ≤
          ∑ g : Fin l × Bool, ∑ i : Fiber g,
            ((consecutiveCell A (a g.1) delta R (parityRep g.2)
              (sg g i).val).card : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        simpa [Fiber] using hsg_avg g
      _ = ∑ g : Fin l × Bool, ∑ i : Fiber g,
          ((packingCell A r c delta R i.val).card : ℝ) := by
        apply Fintype.sum_congr
        exact hfiber_eq
      _ = ∑ i : Fin K, ((packingCell A r c delta R i).card : ℝ) := by
        simpa [Fiber] using sum_owner_parity_fibers o r
          (fun i : Fin K ↦ ((packingCell A r c delta R i).card : ℝ))
      _ = ((packingCellUnion A r c delta R).card : ℝ) := hcardR.symm

end Erdos441
