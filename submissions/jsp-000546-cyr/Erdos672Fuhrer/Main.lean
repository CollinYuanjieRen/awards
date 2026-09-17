import Mathlib

/-!
# Erdős Problem #672: Führer's example `(−6)·(−1)·4·9 = 6³` over the integers

Erdős asked whether the product of an arithmetic progression `n, n+d, …, n+(k−1)d` of positive
integers of length `k ≥ 4` with `gcd(n, d) = 1` can be a perfect power (OPEN for general `k, ℓ`;
not addressed here; Euler's and Obláth's cases are not claimed either).  The problem page
records: "Jakob Führer has observed this is possible for integers in general, for example
`(−6)·(−1)·4·9 = 6³`."  This file verifies that example: the arithmetic progression
`−6, −1, 4, 9` (first term `−6`, difference `5`, coprime) of length `4` has product `6³`, so the
restriction to positive integers in the problem is essential.  The formal-conjectures predicate
`Erdos672With` is stated over `ℕ`, so the integer example is our own statement.
-/

/-- **Erdős #672, Führer's example**: the integer arithmetic progression `−6, −1, 4, 9`
(`n = −6`, `d = 5`, `gcd = 1`, length `4`) has product `6³`. -/
theorem erdos_672_fuhrer_example :
    Int.gcd (-6) 5 = 1 ∧ (∏ i ∈ Finset.range 4, ((-6 : ℤ) + (i : ℤ) * 5)) = 6 ^ 3 := by
  refine ⟨by decide, ?_⟩
  norm_num [Finset.prod_range_succ]

/-- Consequently the positive-integer restriction in the problem is essential: over `ℤ` a coprime
arithmetic progression of length `4` can have a perfect-cube product. -/
theorem erdos_672_exists_int_ap_cube :
    ∃ n d : ℤ, Int.gcd n d = 1 ∧ ∃ q : ℤ, (∏ i ∈ Finset.range 4, (n + (i : ℤ) * d)) = q ^ 3 :=
  ⟨-6, 5, erdos_672_fuhrer_example.1, 6, erdos_672_fuhrer_example.2⟩
