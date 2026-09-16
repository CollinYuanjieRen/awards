import MerLeanExperiment.ParityGroups

namespace Erdos441

theorem sum_owner_parity_multiplicity {K l : ℕ} (o : Fin K → Fin l)
    (r : Fin K → ℤ) (F : Fin l × Bool → ℝ) :
    (∑ g : Fin l × Bool,
      (Fintype.card {i : Fin K // ownerParity o r i = g} : ℝ) * F g) =
      ∑ i : Fin K, F (ownerParity o r i) := by
  classical
  rw [← sum_owner_parity_fibers o r (fun i => F (ownerParity o r i))]
  apply Finset.sum_congr rfl
  intro g _
  have h (i : {i : Fin K // ownerParity o r i = g}) :
      F (ownerParity o r i.val) = F g := by rw [i.property]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos441

#print axioms Erdos441.sum_owner_parity_multiplicity
