# JSP-000913: Erdős #1100, `τ_⊥(n) ≥ ω(n)` with equality for infinitely many `n`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000913](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000913) / [Erdős Problem #1100](https://www.erdosproblems.com/1100): with `1 = d_1 < ⋯ < d_{τ(n)} = n` the divisors of `n` and `τ_⊥(n)` the number of `i` with `gcd(d_i, d_{i+1}) = 1`, is `τ_⊥(n)/ω(n) → ∞` for almost all `n`, is `τ_⊥(n) < exp((log n)^{o(1)})`, and how does `g(k) = max_{ω(n) = k} τ_⊥(n)` grow?

**Scope statement.** The growth questions are open and are not addressed, nor are the Erdős–Hall and Erdős–Simonovits bounds. The problem page records: "It is trivial that `τ_⊥(n) ≥ ω(n)` (with equality for infinitely many `n`)." This package proves both parts. There is no formal-conjectures statement for #1100, so the definitions are ours: `nextDivisor n d` is the least divisor of `n` exceeding `d` (the successor of `d` among the divisors), `tauPerp n` counts the divisors `d < n` with `gcd(d, nextDivisor n d) = 1` (the consecutive coprime pairs), and `ω(n)` is `n.primeFactors.card`.

## Statement and proof

[Erdos1100TauPerp/Main.lean](Erdos1100TauPerp/Main.lean) proves

```lean
theorem erdos_1100_omega_le_tauPerp (n : ℕ) : n.primeFactors.card ≤ tauPerp n
theorem erdos_1100_eq_infinite : ¬ {n : ℕ | tauPerp n = n.primeFactors.card}.Finite
theorem erdos_1100_remark_closed :
    (∀ n : ℕ, n.primeFactors.card ≤ tauPerp n) ∧
      ¬ {n : ℕ | tauPerp n = n.primeFactors.card}.Finite
```

Proof. For each prime `p ∣ n`, the largest divisor `d < p` of `n` has successor `p` and `gcd(d, p) = 1`; distinct primes give distinct such `d` (`d_p < p ≤ d_q` for `p < q`), so `τ_⊥(n) ≥ ω(n)`. For `n = 2^k` the divisors are `1, 2, …, 2^k` and only the pair `(1, 2)` is coprime, so `τ_⊥(2^k) = 1 = ω(2^k)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
