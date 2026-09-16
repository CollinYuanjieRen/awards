import Jsp937.Definitions

/-! Pointwise bounds for the exterior tails of a Lebesgue function. -/
namespace Jsp937
open Randy1153
noncomputable section

/-- To the left of every node, the Lebesgue function is bounded by its value at `-1`. -/
theorem lebesgueFunction_le_left_endpoint {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (ht : -1 ≤ t) (hleft : ∀ i : Fin n, t ≤ nodes.point i) :
    lebesgueFunction nodes t ≤ lebesgueFunction nodes (-1) := by
  classical
  simp only [lebesgueFunction]
  apply Finset.sum_le_sum
  intro k _
  simp only [lagrangeFundamental, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_div, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonpos (sub_nonpos.mpr (hleft i)),
      abs_of_nonpos (sub_nonpos.mpr (nodes.mem_Icc i).1)]
    linarith

/-- To the right of every node, the Lebesgue function is bounded by its value at `1`. -/
theorem lebesgueFunction_le_right_endpoint {n : ℕ} (nodes : NodeFamily n) (t : ℝ)
    (ht : t ≤ 1) (hright : ∀ i : Fin n, nodes.point i ≤ t) :
    lebesgueFunction nodes t ≤ lebesgueFunction nodes 1 := by
  classical
  simp only [lebesgueFunction]
  apply Finset.sum_le_sum
  intro k _
  simp only [lagrangeFundamental, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_div, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    rw [abs_of_nonneg (sub_nonneg.mpr (hright i)),
      abs_of_nonneg (sub_nonneg.mpr (nodes.mem_Icc i).2)]
    linarith

end
end Jsp937
