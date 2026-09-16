import Erdos1183Chain

#print axioms erdos_1183_f_lower_bound
#print axioms exists_monochromatic_closed_family

/-- Erdős Problem #1183, the chain lower bound `f(n) ≥ (n + 1) / 2`. -/
example (n : ℕ) : n + 1 ≤ 2 * f n :=
  erdos_1183_f_lower_bound n

/-- `f` is the problem's Ramsey function: the supremum of the guaranteed sizes. -/
example (n : ℕ) : f n = sSup {k : ℕ | ∀ c : Finset (Fin n) → Fin 2,
    ∃ F : Finset (Finset (Fin n)), IsMonochromatic c F ∧ IsUnionInterClosed F ∧ k ≤ F.card} :=
  rfl
