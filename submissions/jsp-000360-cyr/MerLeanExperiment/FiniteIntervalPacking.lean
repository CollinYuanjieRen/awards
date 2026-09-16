import MerLeanExperiment.IntervalPacking

namespace Erdos441

theorem eventually_finite_interval_packing {I E : Type*} [Fintype I] [Fintype E]
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : E → I) (r : E → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i ≠ j → ((r j - r i).natAbs : ℝ) ≤ a (o i) * a (o j))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i : E, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) ≤
        1 + epsilon := by
  classical
  let ie : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ee : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let owner : Fin (Fintype.card E) → Fin (Fintype.card I) := fun i => ie.symm (o (ee i))
  have hdis (i j : Fin (Fintype.card I)) (hij : i ≠ j) :
      Disjoint (Set.Ioc (a (ie i)) (b (ie i))) (Set.Ioc (a (ie j)) (b (ie j))) :=
    hdisj _ _ (fun h => hij (ie.injective h))
  have hs (i j : Fin (Fintype.card E)) (hij : i < j) :
      ((r (ee j) - r (ee i)).natAbs : ℝ) ≤ a (ie (owner i)) * a (ie (owner j)) := by
    have hh := hsep (ee i) (ee j) (fun h => (ne_of_lt hij) (ee.injective h))
    simpa [owner] using hh
  obtain ⟨N0, hN0⟩ := eventually_interval_packing (fun i => a (ie i)) (fun i => b (ie i))
    (fun i => ha (ie i)) (fun i => hab (ie i)) hdis owner (fun i => r (ee i))
    (hr.comp ee.injective) hs epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hh := hN0 N hN A hA
  have heq : (∑ i : Fin (Fintype.card E),
      intervalDensity A (a (ie (owner i))) (b (ie (owner i))) (Real.sqrt (N : ℝ))) =
      ∑ i : E, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) := by
    exact Fintype.sum_equiv ee _ _ (fun i => by simp [owner])
  rw [heq] at hh
  exact hh

end Erdos441

#print axioms Erdos441.eventually_finite_interval_packing
