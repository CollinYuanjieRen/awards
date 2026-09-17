import Mathlib

namespace SumsAvoidB

theorem sums_avoid (A B : Finset ℕ) (hB : B.Nonempty) :
    ∀ x ∈ A.filter (fun a => B.max' hB < 2 * a),
    ∀ y ∈ A.filter (fun a => B.max' hB < 2 * a), x + y ∉ B := by
  intro x hx y hy hmem
  rw [Finset.mem_filter] at hx hy
  have hle : x + y ≤ B.max' hB := Finset.le_max' B (x + y) hmem
  have hx2 := hx.2
  have hy2 := hy.2
  omega

#print axioms SumsAvoidB.sums_avoid

end SumsAvoidB
