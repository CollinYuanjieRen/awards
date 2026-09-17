# JSP-000986: Erdős #1181, the primorial below `q(n, k)` divides `∏_{1 ≤ i ≤ k} (n + i)`

This package submits, for intake and eligibility review, a Lean proof of an observation recorded on the page of [JSP-000986](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000986) / [Erdős Problem #1181](https://www.erdosproblems.com/1181): with `q(n, k)` the least prime not dividing `∏_{1 ≤ i ≤ k} (n + i)`, is there `c > 0` with `q(n, log n) < (1 − c)(log n)²` for all large `n`?

**Scope statement.** The question is open and is not addressed, nor is the asymptotic upper bound `q(n, log n) ≤ (1 + o(1))(log n)²`. The problem page records: "The upper bound `q(n, log n) ≤ (1 + o(1))(log n)²` follows from observing that the primorial of `q(n, k)` is at most `∏_{1 ≤ i ≤ k} (n + i)`." This package proves that observation in its precise form: every prime below `q(n, k)` divides the product (by minimality), so the product of the primes below `q(n, k)` — Mathlib's `primorial (q(n, k) − 1)` — divides, hence is at most, `∏_{1 ≤ i ≤ k} (n + i)`. (The prime `q(n, k)` itself does not divide the product, so the page's phrase is read as the primorial of the primes below `q(n, k)`.) There is no formal-conjectures statement for #1181, so the definition of `q` is ours.

## Statement and proof

[Erdos1181Primorial/Main.lean](Erdos1181Primorial/Main.lean) defines

```lean
def intervalProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
noncomputable def q (n k : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ ¬ p ∣ intervalProd n k}
```

and proves

```lean
theorem erdos_1181_primorial_dvd (n k : ℕ) : primorial (q n k - 1) ∣ intervalProd n k
theorem erdos_1181_primorial_le (n k : ℕ) : primorial (q n k - 1) ≤ intervalProd n k
theorem erdos_1181_primorial_le_closed : ¬ ∃ n k : ℕ, intervalProd n k < primorial (q n k - 1)
```

together with `q n k` being a prime not dividing the product and every smaller prime dividing it.

Proof. A prime larger than the product does not divide it, so `q(n, k)` exists; by minimality every prime `p < q(n, k)` divides the product; the product of these distinct primes therefore divides it, and the product is positive.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
