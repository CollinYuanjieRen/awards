import Erdos673Divisors

open Erdos673

#print axioms Erdos673.erdos_673_closed
#print axioms Erdos673.erdos_673
#print axioms Erdos673.erdos_673_average
#print axioms Erdos673.card_divisors_div_le_mul_G
#print axioms Erdos673.G_le_card_divisors
#print axioms Erdos673.densityZero_card_divisors_le
#print axioms Erdos673.card_no_prime_factor_le

/-- Erdős Problem 673: `G(n) → ∞` for almost all `n` (every threshold has an exceptional set of
natural density zero), and `G` grows on average. -/
example : (∀ T : ℝ, DensityZero {n : ℕ | G n ≤ T}) ∧
    Filter.Tendsto (fun X : ℕ => (∑ n ∈ Finset.Icc 1 X, G n) / X) Filter.atTop Filter.atTop :=
  Erdos673.erdos_673_closed

/-- The almost-all statement alone. -/
example (T : ℝ) : DensityZero {n : ℕ | G n ≤ T} := Erdos673.erdos_673 T

/-- Tao's sandwich, lower half: `τ(n/m)/m ≤ G(n)` for `m ∣ n`, `m > 1`. -/
example (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((Nat.divisors (n / m)).card : ℝ) / m ≤ G n :=
  Erdos673.card_divisors_div_le_mul_G hn hm hmn

/-- Tao's sandwich, upper half: `G(n) ≤ τ(n)`. -/
example (n : ℕ) : G n ≤ (Nat.divisors n).card := Erdos673.G_le_card_divisors n

-- The definitions, printed in full.
#print Erdos673.nextDiv
#print Erdos673.G
#print Erdos673.DensityZero
