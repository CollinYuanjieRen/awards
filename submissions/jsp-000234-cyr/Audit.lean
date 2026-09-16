import Erdos273Selfridge

#print axioms erdos_273_three
#print axioms selfridge_covers
#print axioms selfridgeSystem_moduli

/-- Erdős #273 with `p = 3` allowed, in the formal-conjectures shape of `erdos_273.variants.three`
(its `answer(True)` content). -/
example : ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧
    c.moduli i = Ideal.span {↑(p - 1)} := erdos_273_three

/-- The witness covers every natural number. -/
example (n : ℕ) : ∃ i, n % selfridgeModulus i = selfridgeResidue i := selfridge_covers n
