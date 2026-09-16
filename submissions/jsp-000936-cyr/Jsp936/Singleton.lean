import Jsp936.Bounds

/-! The one-node case of the free-node optimization problem. -/
namespace Jsp936
open Randy1153
noncomputable section

/-- A one-node family has constant Lebesgue function equal to one. -/
@[simp]
lemma lebesgueFunction_singleton (nodes : NodeFamily 1) (t : ℝ) :
    lebesgueFunction nodes t = 1 := by
  simp [lebesgueFunction, lagrangeFundamental]

/-- The Lebesgue maximum of a one-node family is one on `[-1, 1]`. -/
@[simp]
lemma lebesgueOn_singleton (nodes : NodeFamily 1) :
    lebesgueOn nodes (-1) 1 = 1 := by
  obtain ⟨t, _, ht, _⟩ := exists_lebesgueOn_eq_and_ge nodes (by norm_num : (-1 : ℝ) ≤ 1)
  rw [ht, lebesgueFunction_singleton]

/-- Every single interpolation node is optimal, with amplification exactly one. -/
theorem singleton_nodes_optimal (nodes : NodeFamily 1) :
    IsOptimal nodes ∧ lebesgueOn nodes (-1) 1 = 1 := by
  constructor
  · intro other
    rw [lebesgueOn_singleton nodes, lebesgueOn_singleton other]
  · exact lebesgueOn_singleton nodes

end
end Jsp936
