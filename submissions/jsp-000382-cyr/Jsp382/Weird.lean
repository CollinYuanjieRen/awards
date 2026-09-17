import Mathlib

namespace Weird

/-- `n` is weird: abundant but not semiperfect. -/
def IsWeird (n : ℕ) : Prop :=
  n < ∑ d ∈ n.properDivisors, d ∧
  ¬ ∃ S ∈ (n.properDivisors).powerset, ∑ d ∈ S, d = n

theorem seventy_abundant : 70 < ∑ d ∈ (70:ℕ).properDivisors, d := by
  decide

set_option maxRecDepth 4000 in
theorem seventy_not_semiperfect :
    ¬ ∃ S ∈ ((70:ℕ).properDivisors).powerset, ∑ d ∈ S, d = 70 := by
  decide

theorem seventy_isWeird : IsWeird 70 :=
  ⟨seventy_abundant, seventy_not_semiperfect⟩

#print axioms Weird.seventy_abundant
#print axioms Weird.seventy_not_semiperfect
#print axioms Weird.seventy_isWeird

end Weird
