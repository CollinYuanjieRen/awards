import MerLeanExperiment.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Tactic

/-! Counting conventions and eventual versus uniform discrepancy bounds. -/

namespace Kesten

/-- The cast visit count is the finite sum of its real-valued Boolean indicators. -/
lemma countInIco_cast_eq_sum (α u v : ℝ) (n : ℕ) :
    (countInIco α u v n : ℝ) =
      ∑ j ∈ Finset.range n,
        if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < v then (1 : ℝ) else 0 := by
  classical
  rw [countInIco, Finset.card_filter]
  push_cast
  rfl

/-- The counting discrepancy is the sum of the centered real-valued indicators. -/
lemma count_discrepancy_eq_sum (α u v : ℝ) (n : ℕ) :
    (countInIco α u v n : ℝ) - (n : ℝ) * (v - u) =
      ∑ j ∈ Finset.range n,
        ((if u ≤ Int.fract (α * (j + 1 : ℕ)) ∧
            Int.fract (α * (j + 1 : ℕ)) < v then (1 : ℝ) else 0) - (v - u)) := by
  rw [countInIco_cast_eq_sum, Finset.sum_sub_distrib]
  simp
  ring

/-- Eventual boundedness of the counting discrepancy is equivalent to one bound valid for
every finite counting time. -/
theorem hasBoundedRemainder_iff_forall (α u v : ℝ) :
    HasBoundedRemainder α u v ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(countInIco α u v n : ℝ) - (n : ℝ) * (v - u)| ≤ C := by
  constructor
  · rintro ⟨C, hC, N, htail⟩
    let D : ℕ → ℝ := fun n ↦
      (countInIco α u v n : ℝ) - (n : ℝ) * (v - u)
    refine ⟨C + ∑ i ∈ Finset.range N, |D i|, ?_, ?_⟩
    · positivity
    · intro n
      change |D n| ≤ C + ∑ i ∈ Finset.range N, |D i|
      by_cases hn : N ≤ n
      · exact (htail n hn).trans <| le_add_of_nonneg_right <| by positivity
      · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
        have hsmall : |D n| ≤ ∑ i ∈ Finset.range N, |D i| :=
          Finset.single_le_sum (fun i _ ↦ abs_nonneg (D i)) hnmem
        exact hsmall.trans <| le_add_of_nonneg_left hC
  · rintro ⟨C, hC, hall⟩
    exact ⟨C, hC, 0, fun n _ ↦ hall n⟩

end Kesten
