import MerLeanExperiment.AveragedMesh
import MerLeanExperiment.ParityDensityMesh
import MerLeanExperiment.FiberMultiplicity

namespace Erdos441

theorem exists_finite_parity_density_mesh {K l : ℕ} (A : Finset ℕ)
    (a b : Fin l → ℝ) (o : Fin K → Fin l) (r : Fin K → ℤ)
    (m : Fin l → ℕ) (delta R : ℝ) (hd : 0 < delta) (hR : 0 < R)
    (hm : ∀ j, 0 < m j) (hKm : ∀ j, K ≤ m j)
    (hlo : ∀ j, (m j : ℝ) * delta ≤ b j - a j)
    (hhi : ∀ j, b j - a j < ((m j : ℝ) + 1) * delta)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) :
    ∃ c : Fin K → ℝ, (∀ i, a (o i) ≤ c i ∧ c i + delta ≤ b (o i)) ∧
      delta * R * (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) R (r i)) ≤
        (packingCellUnion A r c delta R).card +
          delta * (delta * R + 1) * (∑ i : Fin K, 1 / (b (o i) - a (o i))) := by
  classical
  obtain ⟨c, hcb, havg⟩ := exists_averaged_mesh A a b o r m delta R hd hR hm hKm hlo hdisj
  refine ⟨c, hcb, ?_⟩
  let C : Fin l × Bool → ℝ := fun g =>
    ∑ s : Fin (m g.1), ((consecutiveCell A (a g.1) delta R (parityRep g.2) s.val).card : ℝ)
  have hsum : (∑ i : Fin K, C (ownerParity o r i) / m (o i)) ≤
      (packingCellUnion A r c delta R).card := by
    calc
      _ = ∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) * (C g / m g.1) :=
        (sum_owner_parity_multiplicity o r (fun g => C g / m g.1)).symm
      _ = ∑ g : Fin l × Bool,
          (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) / m g.1 * C g := by
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ ≤ _ := havg
  have hper (i : Fin K) :
      delta * R * parityDensity A (a (o i)) (b (o i)) R (r i) ≤
        C (ownerParity o r i) / m (o i) +
          delta * (delta * R + 1) / (b (o i) - a (o i)) := by
    have hdens : parityDensity A (a (o i)) (b (o i)) R (r i) =
        parityDensity A (a (o i)) (b (o i)) R (parityRep (decide (Even (r i)))) := by
      change ((parityRegion A (a (o i)) (b (o i)) R (r i)).card : ℝ) / _ =
        ((parityRegion A (a (o i)) (b (o i)) R (parityRep (decide (Even (r i))))).card : ℝ) / _
      rw [parity_region_rep]
    rw [hdens]
    exact parity_density_mesh_bound A (a (o i)) (b (o i)) delta R
      (parityRep (decide (Even (r i)))) (m (o i)) (hm (o i)) hd hR (hlo (o i)) (hhi (o i))
  have hall := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) => hper i)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hall
  have herr : (∑ i : Fin K, delta * (delta * R + 1) / (b (o i) - a (o i))) =
      delta * (delta * R + 1) * (∑ i : Fin K, 1 / (b (o i) - a (o i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr] at hall
  linarith

end Erdos441

#print axioms Erdos441.exists_finite_parity_density_mesh
