import MerLeanExperiment.GridColumns
import MerLeanExperiment.IntTelescoping

namespace Erdos441

theorem sum_gridCount_column (q : ℝ) (hq : 1 < q) (L : ℕ) (T t j : ℤ)
    (ht : -T ≤ t) (hj : -T ≤ j) (hjL : j < (L : ℤ)) :
    ∑ i ∈ Finset.Icc (-T) t, (gridCount q L i j : ℝ) = (gridA q t j).card := by
  have hzero : gridA q (-T - 1) j = ∅ := by
    simp [gridA, show ¬ j ≤ -T - 1 by omega]
  calc
    _ = ∑ i ∈ Finset.Icc (-T) t,
        ((gridA q i j \ gridA q (i - 1) j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [gridCount, ne_of_lt hjL, hjL]
    _ = (gridA q t j).card - (gridA q (-T - 1) j).card :=
      sum_card_sdiff_Icc (fun i => gridA q i j) (-T) t (by omega)
        (fun i _ => grid_column_mono q hq (i - 1) i j (by omega))
    _ = _ := by rw [hzero]; simp

theorem grid_capacity_prefix_eq (q : ℝ) (hq : 1 < q) (L : ℕ) (hL : 1 ≤ L)
    (T t : ℤ) (hT : 0 ≤ T) (ht : -T ≤ t) :
    gridCapacityPrefix q L T t =
      (∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1)) +
      (1 / 2 : ℝ) * (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1))) +
      (if 0 ≤ t then 1 - q ^ (-1 : ℤ) else 0) := by
  classical
  let f : ℤ → ℝ := fun j => gridDelta q L j *
    ∑ i ∈ Finset.Icc (-T) t, (gridCount q L i j : ℝ)
  have hsum : gridCapacityPrefix q L T t = ∑ j ∈ Finset.Icc (-T) (L : ℤ), f j := by
    unfold gridCapacityPrefix
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.mul_sum _ _ _).symm
  have hsplit : Finset.Icc (-T) (L : ℤ) =
      (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1)) ∪ {(L : ℤ)} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have hdis1 : Disjoint (Finset.Icc (-T) (-1)) (Finset.Icc 0 ((L : ℤ) - 1)) := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_Icc] at hj hk
    omega
  have hdis2 : Disjoint (Finset.Icc (-T) (-1) ∪ Finset.Icc 0 ((L : ℤ) - 1))
      {(L : ℤ)} := by
    rw [Finset.disjoint_left]
    intro j hj hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hj hk
    omega
  rw [hsum, hsplit, Finset.sum_union hdis2, Finset.sum_union hdis1, Finset.sum_singleton]
  have hneg : (∑ j ∈ Finset.Icc (-T) (-1), f j) =
      ∑ j ∈ Finset.Icc (-T) (-1), (gridA q t j).card * q ^ j * (q - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    dsimp [f]
    rw [sum_gridCount_column q hq L T t j ht hjlo (by omega)]
    simp [gridDelta, show j < 0 by omega]
    ring
  have hpos : (∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1), f j) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 0 ((L : ℤ) - 1),
        (gridA q t j).card * (q - 1) * (q ^ j - q ^ (-j - 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hj
    dsimp [f]
    rw [sum_gridCount_column q hq L T t j ht (by omega) (by omega)]
    simp [gridDelta, not_lt.mpr hjlo, show j < (L : ℤ) by omega]
    ring
  have hlast : f (L : ℤ) = if 0 ≤ t then 1 - q ^ (-1 : ℤ) else 0 := by
    dsimp [f]
    have hd : gridDelta q L (L : ℤ) = 1 - q ^ (-1 : ℤ) := by
      simp [gridDelta]
    rw [hd]
    have hnegT : -T ≤ 0 := by omega
    by_cases ht0 : 0 ≤ t
    · simp [gridCount, Finset.sum_ite_eq', hnegT, ht0]
    · simp [gridCount, Finset.sum_ite_eq', hnegT, ht0]
  rw [hneg, hpos, hlast]

end Erdos441
