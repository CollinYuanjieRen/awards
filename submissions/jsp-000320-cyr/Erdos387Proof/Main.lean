import Erdos387Proof.MainAssembly
import Erdos387Proof.ConvenientError
import Erdos387Proof.SeparatedError

/-! The unconditional negative answer to Erdős Problem 387 (Bui–Naprienko–Pratt–Zaharescu). -/

set_option autoImplicit false

namespace Erdos387Proof

/-- There is no absolute constant `c > 0` such that every binomial coefficient
`n.choose k`, `1 ≤ k < n`, has a divisor in the interval `(c * n, n]`. -/
theorem not_exists_uniform_close_divisor :
  ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k :=
  MainAssembly.main_of_limits
    (fun S hB => ConvenientError.tendsto_convenient_card_div_sieveScale_zero S hB)
    (fun S hB => SeparatedError.tendsto_separated_card_div_sieveScale_zero S hB)

end Erdos387Proof
