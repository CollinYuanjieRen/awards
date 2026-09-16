import MerLeanExperiment.CyclicAverage

namespace Erdos441

theorem exists_injective_average {I : Type*} [Fintype I] (m : ℕ) (hm : 0 < m)
    (hk : Fintype.card I ≤ m) (f : Fin m → ℝ) :
    ∃ s : I → Fin m, Function.Injective s ∧
      (Fintype.card I : ℝ) / m * (∑ j : Fin m, f j) ≤ ∑ i : I, f (s i) := by
  classical
  obtain ⟨offset, hinj, hbound⟩ := exists_cyclic_average m (Fintype.card I) hm hk f
  let e := Fintype.equivFin I
  let s : I → Fin m := fun i => offset + Fin.castLE hk (e i)
  refine ⟨s, hinj.comp e.injective, ?_⟩
  have heq : (∑ i : I, f (s i)) =
      ∑ h : Fin (Fintype.card I), f (offset + Fin.castLE hk h) := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [heq]
  exact hbound

end Erdos441

#print axioms Erdos441.exists_injective_average
