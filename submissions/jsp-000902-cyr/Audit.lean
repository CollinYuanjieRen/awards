import Erdos1085Lenz

open Filter Finset

#print axioms erdos_1085_lower_d4_lenz
#print axioms lenz_lower_bound

/-- Erdős #1085, Lenz's lower bound, in the formal-conjectures shape
`erdos_1085.variants.lower_d4_lenz`. -/
example {d : ℕ} (hd : 4 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 - C ≤ f d n := erdos_1085_lower_d4_lenz hd

/-- The definitions are the formal-conjectures ones. -/
example (d n : ℕ) : f d n = ⨆ (s : Finset (EuclideanSpace ℝ (Fin d))) (_ : s.card = n), unitDistNum s := rfl
