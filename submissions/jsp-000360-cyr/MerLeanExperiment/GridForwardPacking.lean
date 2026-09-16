import MerLeanExperiment.GridFibers
import MerLeanExperiment.FiniteIntervalPacking

namespace Erdos441

theorem grid_intervals_disjoint (q : ℝ) (hq : 1 < q) (i j : ℤ) (hij : i ≠ j) :
    Disjoint (Set.Ioc (q ^ i) (q ^ (i + 1))) (Set.Ioc (q ^ j) (q ^ (j + 1))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := zpow_le_zpow_right₀ hq.le (show i + 1 ≤ j by omega)
    exact (h.trans_lt hy.1).not_ge hx.2
  · have h := zpow_le_zpow_right₀ hq.le (show j + 1 ≤ i by omega)
    exact (h.trans_lt hx.1).not_ge hy.2

theorem eventually_grid_forward_packing {I : Type*} [Fintype I]
    (q : ℝ) (hq : 1 < q) (L : ℕ) (j : ℤ) (row : I → ℤ)
    (hrow : Function.Injective row) (phi : I → I) (hphi : ∀ i, row i ≤ row (phi i))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      (∑ i : I, (gridCount q L (row i) j : ℝ) *
        intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
          (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
  classical
  let E : Type _ := Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j}
  let label : E → ℤ := fun e => e.2.val
  let owner : E → I := fun e => phi e.1
  have hqp : 0 < q := by linarith
  have ha (i : I) : 0 < q ^ row i := zpow_pos hqp _
  have hab (i : I) : q ^ row i < q ^ (row i + 1) := by
    rw [zpow_add₀ hqp.ne', zpow_one]
    nlinarith [ha i]
  have hdis (i k : I) (hik : i ≠ k) :
      Disjoint (Set.Ioc (q ^ row i) (q ^ (row i + 1)))
        (Set.Ioc (q ^ row k) (q ^ (row k + 1))) :=
    grid_intervals_disjoint q hq (row i) (row k) (fun h => hik (hrow h))
  have hr : Function.Injective label := grid_fiber_label_injective q hq L j row hrow
  have hsep (e f : E) (_hef : e ≠ f) :
      ((label f - label e).natAbs : ℝ) ≤ q ^ row (owner e) * q ^ row (owner f) := by
    calc
      _ ≤ q ^ row f.1 * q ^ row e.1 := grid_fiber_separation q hq L
        (row f.1) (row e.1) j f.2.val e.2.val f.2.property e.2.property
      _ = q ^ row e.1 * q ^ row f.1 := mul_comm _ _
      _ ≤ _ := mul_le_mul (zpow_le_zpow_right₀ hq.le (hphi e.1))
        (zpow_le_zpow_right₀ hq.le (hphi f.1)) (ha f.1).le (ha (owner e)).le
  obtain ⟨N0, hN0⟩ := eventually_finite_interval_packing
    (fun i => q ^ row i) (fun i => q ^ (row i + 1)) ha hab hdis owner label hr hsep
    epsilon hepsilon
  refine ⟨N0, ?_⟩
  intro N hN A hA
  have hh := hN0 N hN A hA
  have heq := grid_fiber_sum q L j row
    (fun i => intervalDensity A (q ^ row (phi i)) (q ^ (row (phi i) + 1)) (Real.sqrt (N : ℝ)))
  change (∑ e : E, intervalDensity A (q ^ row (phi e.1))
    (q ^ (row (phi e.1) + 1)) (Real.sqrt (N : ℝ))) ≤ _ at hh
  rw [heq] at hh
  exact hh

theorem eventually_uniform_grid_forward_packing {I J : Type*} [Fintype I] [Fintype J]
    (q : ℝ) (hq : 1 < q) (L : ℕ) (col : J → ℤ) (row : I → ℤ)
    (hrow : Function.Injective row) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ, LcmBounded N A →
      ∀ j : J, ∀ phi : I → I, (∀ i, row i ≤ row (phi i)) →
        (∑ i : I, (gridCount q L (row i) (col j) : ℝ) *
          intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
            (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
  classical
  have hex (j : J) (phi : I → I) : ∃ N0 : ℕ, ∀ N ≥ N0, ∀ A : Finset ℕ,
      LcmBounded N A → (∀ i, row i ≤ row (phi i)) →
        (∑ i : I, (gridCount q L (row i) (col j) : ℝ) *
          intervalDensity A (q ^ (row (phi i))) (q ^ (row (phi i) + 1))
            (Real.sqrt (N : ℝ))) ≤ 1 + epsilon := by
    by_cases hphi : ∀ i, row i ≤ row (phi i)
    · obtain ⟨N0, hh⟩ := eventually_grid_forward_packing q hq L (col j) row hrow phi hphi
        epsilon hepsilon
      exact ⟨N0, fun N hN A hA _ => hh N hN A hA⟩
    · exact ⟨0, fun _ _ _ _ h => False.elim (hphi h)⟩
  choose bound hbound using hex
  refine ⟨∑ j : J, ∑ phi : I → I, bound j phi, ?_⟩
  intro N hN A hA j phi hphi
  have h1 : bound j phi ≤ ∑ psi : I → I, bound j psi :=
    Finset.single_le_sum (fun psi _ => Nat.zero_le (bound j psi)) (Finset.mem_univ phi)
  have h2 : (∑ psi : I → I, bound j psi) ≤ ∑ k : J, ∑ psi : I → I, bound k psi :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (∑ psi : I → I, bound k psi))
      (Finset.mem_univ j)
  exact hbound j phi N (h1.trans (h2.trans hN)) A hA hphi

end Erdos441

#print axioms Erdos441.grid_intervals_disjoint
#print axioms Erdos441.eventually_grid_forward_packing
#print axioms Erdos441.eventually_uniform_grid_forward_packing
