import MerLeanExperiment.ParityPacking

namespace Erdos441

theorem eventually_interval_packing {K l : ℕ} (a b : Fin l → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (o : Fin K → Fin l) (r : Fin K → ℤ) (hr : Function.Injective r)
    (hsep : ∀ i j, i < j → ((r j - r i).natAbs : ℝ) ≤ a (o i) * a (o j))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) ≤ 1 + ε := by
  classical
  have hw (x y : ℤ) : (1 : ℝ) ≤ shiftParityWeight x y := by
    unfold shiftParityWeight
    split_ifs <;> norm_num
  have hscale (i j : Fin K) (x y : ℤ) :
      a (o i) * a (o j) ≤ (shiftParityWeight x y : ℝ) * a (o i) * a (o j) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hw x y) (ha (o i)).le) (ha (o j)).le
  have hsep1 (i j : Fin K) (hij : i < j) :
      ((r j - r i).natAbs : ℝ) ≤
        (shiftParityWeight (r i) (r j) : ℝ) * a (o i) * a (o j) :=
    (hsep i j hij).trans (hscale i j (r i) (r j))
  let r' : Fin K → ℤ := fun i => r i + 1
  have hr' : Function.Injective r' := by
    intro i j h
    apply hr
    dsimp [r'] at h
    omega
  have hsep2 (i j : Fin K) (hij : i < j) :
      ((r' j - r' i).natAbs : ℝ) ≤
        (shiftParityWeight (r' i) (r' j) : ℝ) * a (o i) * a (o j) := by
    have heq : r' j - r' i = r j - r i := by dsimp [r']; ring
    rw [heq]
    exact (hsep i j hij).trans (hscale i j (r' i) (r' j))
  obtain ⟨N1, hN1⟩ := eventually_parity_packing a b ha hab hdisj o r hr hsep1
    (ε / 2) (by positivity)
  obtain ⟨N2, hN2⟩ := eventually_parity_packing a b ha hab hdisj o r' hr' hsep2
    (ε / 2) (by positivity)
  refine ⟨max N1 N2, ?_⟩
  intro N hN A hA
  have h1 := hN1 N ((le_max_left _ _).trans hN) A hA
  have h2 := hN2 N ((le_max_right _ _).trans hN) A hA
  have heq : (∑ i : Fin K, intervalDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ))) =
      (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)) +
      (∑ i : Fin K, parityDensity A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r' i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (density_parity_partition A (a (o i)) (b (o i)) (Real.sqrt (N : ℝ)) (r i)).symm
  rw [heq]
  linarith

end Erdos441

#print axioms Erdos441.eventually_interval_packing
