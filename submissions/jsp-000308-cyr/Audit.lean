import Erdos373Solutions

open scoped Nat
open Erdos373

#print axioms erdos_373_trivial_solution
#print axioms erdos_373_trivial_solution_not_mem
#print axioms erdos_373_hickerson_mem
#print axioms erdos_373_remarks_closed

/-- Erdős #373: Hickerson's four solutions are non-trivial solutions. -/
example : (9, [7, 3, 3, 2]) ∈ S ∧ (10, [7, 6]) ∈ S ∧ (10, [7, 5, 3]) ∈ S ∧ (16, [14, 5, 2]) ∈ S :=
  erdos_373_hickerson_mem

/-- The set is the formal-conjectures one. -/
example : S = {(n, l) | n ! = (l.map Nat.factorial).prod ∧ l.Pairwise (· ≥ ·)
    ∧ l.headI < (n - 1 : ℕ) ∧ ∀ a ∈ l, 1 < a } := rfl
