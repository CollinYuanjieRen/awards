import Erdos387Proof

/-! Axiom audit and statement restatement for JSP-000320 / Erdős problem 387. -/

-- the two roots
#print axioms Erdos387Proof.not_exists_uniform_close_divisor
#print axioms Erdos387.erdos_387

-- the assembly and the five-error exhaustion it consumes
#print axioms Erdos387Proof.MainAssembly.main_of_limits
#print axioms Erdos387Proof.SquarefreeErrorExhaustion.exists_counterexample_of_bad_squarefree_card_lt

-- the three error limits proved in this package
#print axioms Erdos387Proof.MediumError.tendsto_medium_card_div_sieveScale_zero
#print axioms Erdos387Proof.ConvenientError.tendsto_convenient_card_div_sieveScale_zero
#print axioms Erdos387Proof.SeparatedError.tendsto_separated_card_div_sieveScale_zero

-- the E1 limit, the unconditional cover with an arbitrarily small E4 budget,
-- and the squarefree candidate lower bound
#print axioms Erdos387Proof.ExistingCountingBounds.tendsto_squarefree_large_div_sieveScale_zero
#print axioms Erdos387Proof.ExistingCountingBounds.exists_cover_with_comparable_budget
#print axioms Erdos387Proof.ExistingCountingBounds.eventually_squarefree_card_ge

-- the analytic input of the covering construction: a genuine theorem, not an assumption
#print axioms Erdos387.shiftedSiegelWalfiszLower

/-- The negative answer to Erdős problem 387, with every auxiliary definition unfolded:
no positive constant `c` makes every binomial coefficient `n.choose k`, `1 ≤ k < n`, have a
divisor in `(c * n, n]`. -/
example : ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k :=
  Erdos387Proof.not_exists_uniform_close_divisor

/-- The canonical `formal-conjectures` face, verbatim except that the official file writes
the left-hand side as `answer(False)`; the `answer` macro elaborates to its argument. -/
example : False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k :=
  Erdos387.erdos_387
