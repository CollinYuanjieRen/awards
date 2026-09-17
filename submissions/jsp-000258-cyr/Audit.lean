import Erdos307Disjoint

open scoped Finset
open Erdos307

#print axioms Erdos307.erdos_307_disjoint_and_two_le
#print axioms erdos_307_easy_closed

/-- Erdős #307: any solution has `P`, `Q` disjoint and reciprocal sum over `P ∪ Q` at least `2`. -/
example {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    Disjoint P Q ∧ 2 ≤ ∑ p ∈ P ∪ Q, (p : ℚ)⁻¹ := erdos_307_disjoint_and_two_le hP hQ heq
