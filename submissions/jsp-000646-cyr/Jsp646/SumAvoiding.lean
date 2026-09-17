import Mathlib

namespace SumAvoiding

theorem sum_avoiding (A : Finset ℕ) (hA : A.Nonempty) :
    ∀ x ∈ A.filter (fun a => A.max' hA < 2 * a),
    ∀ y ∈ A.filter (fun a => A.max' hA < 2 * a), x + y ∉ A := by
  intro x hx y hy hmem
  rw [Finset.mem_filter] at hx hy
  have hle : x + y ≤ A.max' hA := Finset.le_max' A (x + y) hmem
  have hx2 := hx.2
  have hy2 := hy.2
  omega

#print axioms SumAvoiding.sum_avoiding

end SumAvoiding
