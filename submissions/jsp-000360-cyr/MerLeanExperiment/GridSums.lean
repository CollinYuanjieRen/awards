import MerLeanExperiment.GridDefinitions
import MerLeanExperiment.IntTelescoping

namespace Erdos441

theorem sum_Icc_zpow_difference (q : ℝ) (hq : q ≠ 0) (a b : ℤ)
    (hab : a ≤ b + 1) :
    ∑ j ∈ Finset.Icc a b, (q - 1) * (q ^ j - q ^ (-j - 1)) =
      q ^ (b + 1) - q ^ a - q ^ (-a) + q ^ (-b - 1) := by
  have hneg : (∑ j ∈ Finset.Icc a b, (q - 1) * q ^ (-j - 1)) =
      q ^ (-a) - q ^ (-b - 1) := by
    calc
      _ = ∑ j ∈ Finset.Icc a b, (-q ^ (-j - 1) - (-q ^ (-(j - 1) - 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        have hi : -(j - 1) - 1 = -j := by omega
        rw [hi, zpow_sub_one₀ hq]
        field_simp
        ring
      _ = -q ^ (-b - 1) - (-q ^ (-(a - 1) - 1)) :=
        sum_Icc_backward_sub (fun j => -q ^ (-j - 1)) a b hab
      _ = _ := by
        have hi : -(a - 1) - 1 = -a := by omega
        rw [hi]
        ring
  calc
    _ = (∑ j ∈ Finset.Icc a b, q ^ j * (q - 1)) -
        ∑ j ∈ Finset.Icc a b, (q - 1) * q ^ (-j - 1) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [sum_Icc_zpow_mul_sub_one q hq a b hab, hneg]; ring

theorem grid_beta_prefix_eq (q : ℝ) (hq : q ≠ 0) (L : ℕ) (T t : ℤ)
    (hT : 0 ≤ T) (hLt : (L : ℤ) ≤ t) :
    gridBetaPrefix q L T t = q ^ (t + 1) - q ^ (-T) +
      gridEta * (q ^ (t + 1) - q ^ (L : ℤ)) := by
  have hid (i : ℤ) : gridBeta q L i = q ^ i * (q - 1) +
      if (L : ℤ) ≤ i then gridEta * (q ^ i * (q - 1)) else 0 := by
    by_cases hi : i < (L : ℤ)
    · simp [gridBeta, hi, not_le.mpr hi]
    · simp only [gridBeta, ite_eq_right hi, ite_eq_left (not_lt.mp hi)]
      ring
  have hfilter : (Finset.Icc (-T) t).filter (fun i => (L : ℤ) ≤ i) =
      Finset.Icc (L : ℤ) t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hextra :
      (∑ i ∈ Finset.Icc (-T) t,
        if (L : ℤ) ≤ i then gridEta * (q ^ i * (q - 1)) else 0) =
      gridEta * ∑ i ∈ Finset.Icc (L : ℤ) t, q ^ i * (q - 1) := by
    rw [← Finset.sum_filter, hfilter, Finset.mul_sum]
  unfold gridBetaPrefix
  simp_rw [hid]
  rw [Finset.sum_add_distrib, hextra,
    sum_Icc_zpow_mul_sub_one q hq (-T) t (by omega),
    sum_Icc_zpow_mul_sub_one q hq (L : ℤ) t (by omega)]

end Erdos441

#print axioms Erdos441.sum_Icc_zpow_difference
#print axioms Erdos441.grid_beta_prefix_eq
