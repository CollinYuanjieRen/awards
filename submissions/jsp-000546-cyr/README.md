# JSP-000546: Erdős #672, Führer's integer example `(−6)·(−1)·4·9 = 6³`

This package submits, for intake and eligibility review, a Lean proof of the example recorded on the page of [JSP-000546](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000546) / [Erdős Problem #672](https://www.erdosproblems.com/672): can the product of an arithmetic progression `n, n+d, …, n+(k−1)d` of positive integers with `k ≥ 4` and `gcd(n, d) = 1` be a perfect power?

**Scope statement.** The question itself is open and is not addressed; Euler's result for squares with `k = 4` and Obláth's cases are not claimed either. The problem page records: "Jakob Führer has observed this is possible for integers in general, for example `(−6)·(−1)·4·9 = 6³`." This package verifies that example: the integer arithmetic progression `−6, −1, 4, 9` (first term `−6`, difference `5`, coprime, length `4`) has product `6³`, so the restriction to positive integers in the problem is essential. The formal-conjectures predicate `Erdos672With` is stated over `ℕ`, so the integer statement here is ours.

## Statement and proof

[Erdos672Fuhrer/Main.lean](Erdos672Fuhrer/Main.lean) proves

```lean
theorem erdos_672_fuhrer_example :
    Int.gcd (-6) 5 = 1 ∧ (∏ i ∈ Finset.range 4, ((-6 : ℤ) + (i : ℤ) * 5)) = 6 ^ 3
```

and the corollary `erdos_672_exists_int_ap_cube : ∃ n d : ℤ, Int.gcd n d = 1 ∧ ∃ q : ℤ, (∏ i ∈ Finset.range 4, (n + (i : ℤ) * d)) = q ^ 3`.

Proof. `Int.gcd (−6) 5 = Nat.gcd 6 5 = 1` by evaluation, and the product `(−6)·(−1)·4·9 = 216 = 6³` by unfolding `Finset.prod_range_succ` and integer arithmetic.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
