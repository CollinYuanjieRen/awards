import Erdos1188CoveringCount

open Erdos1188

#print axioms erdos_1188_trivial_count
#print axioms erdos_1188_trivial_count_closed

/-- Erdős #1188: without minimality, at least `2^(x − 6)` distinct covering systems have moduli
in `[1, x]` for `x ≥ 12`. -/
example (x : ℕ) (hx : 12 ≤ x) : 2 ^ (x - 6) ≤ distinctCoveringCount x :=
  erdos_1188_trivial_count x hx

/-- The covering-system definitions are the formal-conjectures ones. -/
example (S : Finset CongruenceClass) : Covers S ↔ ∀ z : ℤ, ∃ c ∈ S, Satisfies z c := Iff.rfl
example (c : CongruenceClass) : ValidClass c ↔ 2 ≤ c.1 ∧ c.2 < c.1 := Iff.rfl
