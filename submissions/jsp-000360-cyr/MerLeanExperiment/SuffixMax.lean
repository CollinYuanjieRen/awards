import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Basic

namespace Erdos441

/-- The largest value of `a` at an index no earlier than `i`. -/
noncomputable def suffixMax {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.filter (i ≤ ·)).sup' ⟨i, by simp⟩ a

theorem suffix_max_spec {n : ℕ} (a : Fin n → ℝ) :
    (∀ i, a i ≤ suffixMax a i) ∧ Antitone (suffixMax a) ∧
      ∀ i, ∃ j, i ≤ j ∧ a j = suffixMax a i := by
  constructor
  · intro i
    unfold suffixMax
    exact Finset.le_sup' a (by simp)
  constructor
  · intro i j hij
    unfold suffixMax
    apply Finset.sup'_le
    intro k hk
    apply Finset.le_sup' a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact le_trans hij hk
  · intro i
    obtain ⟨j, hj, hmax⟩ :=
      Finset.exists_mem_eq_sup' (s := Finset.univ.filter (i ≤ ·)) ⟨i, by simp⟩ a
    exact ⟨j, (Finset.mem_filter.mp hj).2, hmax.symm⟩

end Erdos441
