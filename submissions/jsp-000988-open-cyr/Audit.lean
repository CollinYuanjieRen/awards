import Erdos1183Lattices

open Erdos1183

#print axioms Erdos1183.erdos_1183_closed
#print axioms Erdos1183.le_f
#print axioms Erdos1183.f_le
#print axioms Erdos1183.good_lower
#print axioms Erdos1183.not_good_upper
#print axioms Erdos1183.good_iff_le_f
#print axioms Erdos1183.card_closed_le

/-- Erdős Problem 1183, phase-1 bounds: `⌈(n+1)/2⌉ ≤ f(n) ≤ (n+1)²` for every `n`. -/
example : (∀ n : ℕ, (n + 2) / 2 ≤ f n) ∧ (∀ n : ℕ, f n ≤ (n + 1) ^ 2) :=
  Erdos1183.erdos_1183_closed

/-- The lower bound without `f`: every colouring has a monochromatic closed family with at least
`⌈(n+1)/2⌉` members. -/
example (n : ℕ) : Good n ((n + 2) / 2) := Erdos1183.good_lower n

/-- The upper bound without `f`: some colouring has no monochromatic closed family with
`(n+1)² + 1` members. -/
example (n : ℕ) : ¬ Good n ((n + 1) ^ 2 + 1) := Erdos1183.not_good_upper n

/-- `f n` is a maximum, not a junk supremum. -/
example (n m : ℕ) : Good n m ↔ m ≤ f n := Erdos1183.good_iff_le_f

/-- At most `2^(n²+2n)` nonempty families closed under unions and intersections. -/
example (n : ℕ) :
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
      (fun F => F.Nonempty ∧ Closed F)).card ≤ 2 ^ (n ^ 2 + 2 * n) :=
  Erdos1183.card_closed_le n

-- The definitions, printed in full.
#print Erdos1183.Closed
#print Erdos1183.Mono
#print Erdos1183.Good
#print Erdos1183.f
