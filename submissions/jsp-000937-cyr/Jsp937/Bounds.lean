import Jsp937.Definitions

/-! Bounds for the actual maximum of the Lebesgue function on a closed interval. -/
namespace Jsp937
open Randy1153 Set
noncomputable section

/-- The actual Lebesgue maximum is bounded exactly when every value on the interval is
bounded. -/
theorem lebesgueOn_le_iff {n : ℕ} (nodes : NodeFamily n) (a b C : ℝ) (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ C ↔ ∀ t ∈ Icc a b, lebesgueFunction nodes t ≤ C := by
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  constructor
  · intro hC u hu
    calc
      lebesgueFunction nodes u ≤ lebesgueFunction nodes t := hmax u hu
      _ = lebesgueOn nodes a b := heq.symm
      _ ≤ C := hC
  · intro hC
    rw [heq]
    exact hC t ht

/-- Every value on a nonempty closed interval is at most its actual Lebesgue maximum. -/
theorem lebesgueFunction_le_on {n : ℕ} (nodes : NodeFamily n) {a b t : ℝ}
    (hab : a ≤ b) (ht : t ∈ Icc a b) :
    lebesgueFunction nodes t ≤ lebesgueOn nodes a b := by
  exact (lebesgueOn_le_iff nodes a b (lebesgueOn nodes a b) hab).mp le_rfl t ht

/-- Enlarging a nonempty closed interval cannot decrease the actual Lebesgue maximum. -/
theorem lebesgueOn_mono {n : ℕ} (nodes : NodeFamily n) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hca : c ≤ a) (hbd : b ≤ d) :
    lebesgueOn nodes a b ≤ lebesgueOn nodes c d := by
  obtain ⟨t, ht, heq, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [heq]
  exact lebesgueFunction_le_on nodes hcd ⟨hca.trans ht.1, ht.2.trans hbd⟩

end
end Jsp937
