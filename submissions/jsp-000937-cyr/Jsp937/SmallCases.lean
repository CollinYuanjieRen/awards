import Jsp937.GapObjective
import Randy1153.DeBoorPinkus.GapCritical

/-! The one-node and two-node augmented-gap maximin problems. -/
namespace Jsp937
open Randy1153
noncomputable section

/-- A one-node family has constant Lebesgue function one.

This is adapted from the audited JSP-936 singleton calculation. -/
@[simp]
theorem lebesgueFunction_singleton (nodes : NodeFamily 1) (t : ℝ) :
    lebesgueFunction nodes t = 1 := by
  simp [lebesgueFunction, lagrangeFundamental]

/-- Every ordered singleton has augmented objective one. -/
theorem upsilon_singleton_eq_one (nodes : OrderedNodes 1) : upsilon nodes = 1 := by
  apply le_antisymm
  · simpa using upsilon_le_left nodes
  · rw [upsilon]
    apply Finset.le_inf'
    intro i _
    obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
    · rw [localPeak_zero_eq_left, lebesgueFunction_singleton]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [show (0 : Fin 1).succ = Fin.last 1 by rfl, localPeak_last_eq_right,
        lebesgueFunction_singleton]

/-- For two nodes, the unique internal gap height is one. -/
theorem gapHeight_pair_eq_one (nodes : OrderedNodes 2) (i : Fin 1) :
    gapHeight nodes i = 1 := by
  obtain ⟨t, _, ht, _⟩ := exists_gapHeight_eq_eval_gapPolynomial nodes i
  rw [ht, Randy1153.DeBoorPinkus.gapPolynomial_eq_one_of_two_nodes]
  simp

/-- The Lebesgue value at the left ambient endpoint is at least one for two nodes. -/
theorem one_le_pair_left (nodes : OrderedNodes 2) :
    1 ≤ lebesgueFunction nodes.toNodeFamily (-1) := by
  have h := lebesgueFunction_le_left_endpoint nodes.toNodeFamily (nodes.point 0)
    (nodes.neg_one_le 0) fun i ↦ nodes.strictMono.monotone (Fin.zero_le i)
  simpa using h

/-- The Lebesgue value at the right ambient endpoint is at least one for two nodes. -/
theorem one_le_pair_right (nodes : OrderedNodes 2) :
    1 ≤ lebesgueFunction nodes.toNodeFamily 1 := by
  have h := lebesgueFunction_le_right_endpoint nodes.toNodeFamily
    (nodes.point (Fin.last 1)) (nodes.le_one (Fin.last 1)) fun i ↦
      nodes.strictMono.monotone (Fin.le_last i)
  simpa using h

/-- Every ordered pair has augmented objective one. -/
theorem upsilon_pair_eq_one (nodes : OrderedNodes 2) : upsilon nodes = 1 := by
  apply le_antisymm
  · simpa [gapHeight_pair_eq_one] using upsilon_le_gapHeight nodes (0 : Fin 1)
  · exact (le_upsilon_iff nodes 1).mpr
      ⟨fun i ↦ by rw [gapHeight_pair_eq_one], one_le_pair_left nodes, one_le_pair_right nodes⟩

/-- Every ordered singleton has objective one and is globally maximal. -/
theorem singleton_upsilon_and_maximal (nodes : OrderedNodes 1) :
    upsilon nodes = 1 ∧ IsUpsilonMaximizer nodes := by
  refine ⟨upsilon_singleton_eq_one nodes, fun other ↦ ?_⟩
  rw [upsilon_singleton_eq_one other, upsilon_singleton_eq_one nodes]

/-- Every ordered pair has objective one and is globally maximal. -/
theorem pair_upsilon_and_maximal (nodes : OrderedNodes 2) :
    upsilon nodes = 1 ∧ IsUpsilonMaximizer nodes := by
  refine ⟨upsilon_pair_eq_one nodes, fun other ↦ ?_⟩
  rw [upsilon_pair_eq_one other, upsilon_pair_eq_one nodes]

end
end Jsp937
