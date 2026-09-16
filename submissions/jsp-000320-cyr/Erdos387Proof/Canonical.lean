import Erdos387Proof.Main

/-! Canonical face of Erdős Problem 387 as stated in formal-conjectures
(`FormalConjectures/ErdosProblems/387.lean`, pinned in `ref/fc387-official.lean`). There the
statement reads `answer(False) ↔ …`; the `answer` macro elaborates to its argument with a
metadata annotation, so the proposition is `False ↔ …`, copied verbatim below. -/

set_option autoImplicit false

namespace Erdos387

/-- Is there an absolute constant `c > 0` such that, for all `1 ≤ k < n`, the binomial
coefficient `n.choose k` has a divisor in `(c * n, n]`? The answer is no. -/
theorem erdos_387 : False ↔ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k :=
  iff_of_false not_false Erdos387Proof.not_exists_uniform_close_divisor

end Erdos387
