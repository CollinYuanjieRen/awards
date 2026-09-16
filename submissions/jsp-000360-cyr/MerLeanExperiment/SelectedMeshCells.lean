import MerLeanExperiment.ParityGroupDefinitions
import Mathlib.Tactic

namespace Erdos441

theorem selected_mesh_bounds {K l : ℕ} (a b : Fin l → ℝ)
    (o : Fin K → Fin l) (m : Fin l → ℕ) (s : ∀ i : Fin K, Fin (m (o i)))
    (delta : ℝ) (hd : 0 ≤ delta)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j) :
    ∀ i, a (o i) ≤ a (o i) + (s i).val * delta ∧
      a (o i) + (s i).val * delta + delta ≤ b (o i) := by
  intro i
  have hn : (0 : ℝ) ≤ (s i).val := by positivity
  have hi : ((s i).val : ℝ) + 1 ≤ m (o i) := by exact_mod_cast (s i).isLt
  have hh := mul_le_mul_of_nonneg_right hi hd
  constructor
  · nlinarith [mul_nonneg hn hd]
  · nlinarith [hmesh (o i)]

theorem selected_mesh_cells_card {K l : ℕ} (A : Finset ℕ)
    (a b : Fin l → ℝ) (o : Fin K → Fin l) (r : Fin K → ℤ)
    (m : Fin l → ℕ) (s : ∀ i : Fin K, Fin (m (o i))) (delta R : ℝ)
    (hd : 0 < delta) (hR : 0 < R)
    (hmesh : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (hs : ∀ i j, ownerParity o r i = ownerParity o r j →
      (s i).val = (s j).val → i = j) :
    (packingCellUnion A r (fun i => a (o i) + (s i).val * delta) delta R).card =
      ∑ i : Fin K,
        (packingCell A r (fun i => a (o i) + (s i).val * delta) delta R i).card := by
  classical
  let c := fun i => a (o i) + (s i).val * delta
  have hb := selected_mesh_bounds a b o m s delta hd.le hmesh
  have hpw : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint
      (packingCell A r c delta R) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have hi := (Finset.mem_filter.mp hn).2
    have hj := (Finset.mem_filter.mp hn').2
    have hoi : (n : ℝ) / R ∈ Set.Ioc (a (o i)) (b (o i)) := by
      constructor
      · apply (lt_div_iff₀ hR).mpr
        exact (mul_le_mul_of_nonneg_right (hb i).1 hR.le).trans_lt hi.1
      · apply (div_le_iff₀ hR).mpr
        exact hi.2.1.trans (mul_le_mul_of_nonneg_right (hb i).2 hR.le)
    have hoj : (n : ℝ) / R ∈ Set.Ioc (a (o j)) (b (o j)) := by
      constructor
      · apply (lt_div_iff₀ hR).mpr
        exact (mul_le_mul_of_nonneg_right (hb j).1 hR.le).trans_lt hj.1
      · apply (div_le_iff₀ hR).mpr
        exact hj.2.1.trans (mul_le_mul_of_nonneg_right (hb j).2 hR.le)
    have ho : o i = o j := by
      by_contra h
      exact Set.disjoint_left.mp (hdisj (o i) (o j) h) hoi hoj
    have hpar : Even (r i) ↔ Even (r j) :=
      (Int.even_sub.mp hi.2.2).symm.trans (Int.even_sub.mp hj.2.2)
    have hg : ownerParity o r i = ownerParity o r j := by
      simp only [ownerParity, Prod.mk.injEq]
      exact ⟨ho, by simp only [hpar]⟩
    have hindex : (s i).val = (s j).val := by
      by_contra hnij
      rcases lt_or_gt_of_ne hnij with hlt | hgt
      · have hsle : ((s i).val : ℝ) + 1 ≤ (s j).val := by exact_mod_cast hlt
        have hcle : c i + delta ≤ c j := by
          dsimp [c]
          rw [congrArg a ho]
          nlinarith [mul_le_mul_of_nonneg_right hsle hd.le]
        have hscale := mul_le_mul_of_nonneg_right hcle hR.le
        linarith [hi.2.1, hj.1]
      · have hsle : ((s j).val : ℝ) + 1 ≤ (s i).val := by exact_mod_cast hgt
        have hcle : c j + delta ≤ c i := by
          dsimp [c]
          rw [congrArg a ho]
          nlinarith [mul_le_mul_of_nonneg_right hsle hd.le]
        have hscale := mul_le_mul_of_nonneg_right hcle hR.le
        linarith [hj.2.1, hi.1]
    exact hij (hs i j hg hindex)
  exact Finset.card_biUnion hpw

end Erdos441

#print axioms Erdos441.selected_mesh_bounds
#print axioms Erdos441.selected_mesh_cells_card
