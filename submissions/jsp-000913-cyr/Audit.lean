import Erdos1100TauPerp

#print axioms erdos_1100_omega_le_tauPerp
#print axioms erdos_1100_eq_infinite
#print axioms erdos_1100_remark_closed

/-- Erdős #1100: `τ_⊥(n) ≥ ω(n)` for all `n`, with equality for infinitely many `n`. -/
example : (∀ n : ℕ, n.primeFactors.card ≤ tauPerp n) ∧
    ¬ {n : ℕ | tauPerp n = n.primeFactors.card}.Finite := erdos_1100_remark_closed
