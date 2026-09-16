import MerLeanExperiment.GridFiberDefinitions
import MerLeanExperiment.GridColumns
import Mathlib.Tactic

namespace Erdos441

theorem grid_fiber_card (q : ℝ) (L : ℕ) (i j : ℤ) :
    (gridFiber q L i j).card = gridCount q L i j := by
  simp only [gridFiber, gridCount]
  split_ifs <;> rfl

theorem grid_fibers_disjoint (q : ℝ) (hq : 1 < q) (L : ℕ) (i k j : ℤ)
    (hik : i ≠ k) : Disjoint (gridFiber q L i j) (gridFiber q L k j) := by
  by_cases hjL : j = (L : ℤ)
  · subst j
    simp only [gridFiber, ↓reduceIte]
    by_cases hi : i = 0
    · subst i
      have hk : k ≠ 0 := by
        intro hk
        apply hik
        omega
      simp [hk]
    · simp [hi]
  · by_cases hj : j < (L : ℤ)
    · simp only [gridFiber, hjL, hj, ↓reduceIte]
      apply Finset.disjoint_left.mpr
      intro z hzi hzk
      have hziA := (Finset.mem_sdiff.mp hzi).1
      have hzkA := (Finset.mem_sdiff.mp hzk).1
      have hziN := (Finset.mem_sdiff.mp hzi).2
      have hzkN := (Finset.mem_sdiff.mp hzk).2
      rcases lt_or_gt_of_ne hik with hik' | hki'
      · exact hzkN (grid_column_mono q hq i (k - 1) j (by omega) hziA)
      · exact hziN (grid_column_mono q hq k (i - 1) j (by omega) hzkA)
    · simp [gridFiber, hjL, hj]

theorem grid_fiber_separation (q : ℝ) (hq : 1 < q) (L : ℕ)
    (i k j z w : ℤ) (hz : z ∈ gridFiber q L i j)
    (hw : w ∈ gridFiber q L k j) :
    ((z - w).natAbs : ℝ) ≤ q ^ i * q ^ k := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  by_cases hjL : j = (L : ℤ)
  · subst j
    simp only [gridFiber, ↓reduceIte] at hz hw
    split at hz <;> split at hw <;> simp_all
  · have hj : j < (L : ℤ) := by
      by_contra hn
      have : (L : ℤ) < j := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hjL)
      simp [gridFiber, hjL, not_lt.mpr this.le] at hz
    have hz' : z ∈ gridA q i j \ gridA q (i - 1) j := by
      simpa only [gridFiber, hjL, hj, ↓reduceIte] using hz
    have hw' : w ∈ gridA q k j \ gridA q (k - 1) j := by
      simpa only [gridFiber, hjL, hj, ↓reduceIte] using hw
    have hzA : z ∈ gridA q i j := (Finset.mem_sdiff.mp hz').1
    have hwA : w ∈ gridA q k j := (Finset.mem_sdiff.mp hw').1
    have hji : j ≤ i := by
      by_contra hn
      rw [gridA, if_neg hn] at hzA
      simp at hzA
    have hjk : j ≤ k := by
      by_contra hn
      rw [gridA, if_neg hn] at hwA
      simp at hwA
    have hzP : z ∈ gridPoints (q ^ j) (q ^ i) := by
      simpa [gridA, hji] using hzA
    have hwP : w ∈ gridPoints (q ^ j) (q ^ k) := by
      simpa [gridA, hjk] using hwA
    have hsep := grid_points_separation (q ^ j) (q ^ i) (q ^ k)
      (zpow_pos hq0 j)
      (zpow_le_zpow_right₀ hq.le hji)
      (zpow_le_zpow_right₀ hq.le hjk) z w hzP hwP
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hsep

theorem grid_fiber_sum {I : Type*} [Fintype I] (q : ℝ) (L : ℕ) (j : ℤ)
    (row : I → ℤ) (f : I → ℝ) :
    (∑ e : Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j}, f e.1) =
      ∑ i : I, (gridCount q L (row i) j : ℝ) * f i := by
  classical
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro i
  simp [grid_fiber_card, mul_comm]

theorem grid_fiber_label_injective {I : Type*} (q : ℝ) (hq : 1 < q) (L : ℕ)
    (j : ℤ) (row : I → ℤ) (hrow : Function.Injective row) :
    Function.Injective
      (fun e : Σ i : I, {z : ℤ // z ∈ gridFiber q L (row i) j} => e.2.val) := by
  rintro ⟨i, z⟩ ⟨k, w⟩ heq
  change z.val = w.val at heq
  have hr : row i = row k := by
    by_contra hne
    have hd := grid_fibers_disjoint q hq L (row i) (row k) j hne
    exact (Finset.disjoint_left.mp hd z.property (by
      rw [heq]
      exact w.property))
  have hik : i = k := hrow hr
  subst k
  congr 1
  exact Subtype.ext heq

end Erdos441
