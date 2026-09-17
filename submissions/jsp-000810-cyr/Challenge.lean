import Mathlib

/-! Comparator-style challenge module (Mathlib-only; targets with `sorry`, not imported by the build)
for JSP-000810 / Erdős #977: the prime-factor lower bound for prime Mersenne exponents. -/

namespace Challenge977

/-- For an odd prime `p`, every prime `q` dividing `2^p - 1` satisfies `2p+1 ≤ q`. -/
theorem two_mul_add_one_le_of_prime_dvd {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {q : ℕ} (hq : q.Prime) (hqd : q ∣ 2 ^ p - 1) : 2 * p + 1 ≤ q := by
  sorry

end Challenge977
