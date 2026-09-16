import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic

namespace ReciprocalSquares

/-- Two distinct finite sets with equal sums of positive weights have nonempty
differences of equal weight. This is the final finite cancellation step. -/
theorem nonempty_sdiffs_of_sum_eq
    (Z D Y : Finset ℕ) (w : ℕ → ℚ)
    (hw : ∀ n ∈ Z, 0 < w n) (hD : D ⊆ Z) (hY : Y ⊆ Z)
    (hne : D ≠ Y) (hsum : ∑ n ∈ D, w n = ∑ n ∈ Y, w n) :
    (D \ Y).Nonempty ∧ (Y \ D).Nonempty ∧
      ∑ n ∈ D \ Y, w n = ∑ n ∈ Y \ D, w n := by
  have hDdecomp :
      (∑ n ∈ D \ Y, w n) + ∑ n ∈ D ∩ Y, w n = ∑ n ∈ D, w n := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter D Y)]
    rw [Finset.sdiff_union_inter]
  have hYdecomp :
      (∑ n ∈ Y \ D, w n) + ∑ n ∈ D ∩ Y, w n = ∑ n ∈ Y, w n := by
    rw [Finset.inter_comm D Y]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter Y D)]
    rw [Finset.sdiff_union_inter]
  have hdiff : ∑ n ∈ D \ Y, w n = ∑ n ∈ Y \ D, w n := by
    linarith
  have hDdiff : D \ Y ⊆ Z := Finset.sdiff_subset.trans hD
  have hYdiff : Y \ D ⊆ Z := Finset.sdiff_subset.trans hY
  have hDY : (D \ Y).Nonempty := by
    by_contra hnonempty
    have hempty : D \ Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hYD : (Y \ D).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hYsubD
      apply hne
      exact Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.mp hempty) hYsubD
    have hpos : 0 < ∑ n ∈ Y \ D, w n :=
      Finset.sum_pos (fun n hn ↦ hw n (hYdiff hn)) hYD
    have hzero : ∑ n ∈ Y \ D, w n = 0 := by
      simpa [hempty] using hdiff.symm
    exact (ne_of_gt hpos) hzero
  have hYD : (Y \ D).Nonempty := by
    by_contra hnonempty
    have hempty : Y \ D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hpos : 0 < ∑ n ∈ D \ Y, w n :=
      Finset.sum_pos (fun n hn ↦ hw n (hDdiff hn)) hDY
    have hzero : ∑ n ∈ D \ Y, w n = 0 := by
      simpa [hempty] using hdiff
    exact (ne_of_gt hpos) hzero
  exact ⟨hDY, hYD, hdiff⟩

end ReciprocalSquares
