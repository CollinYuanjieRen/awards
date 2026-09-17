# JSP-000707: Erdős #854, all gaps between integers coprime to a primorial are even

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000707](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000707) / [Erdős Problem #854](https://www.erdosproblems.com/854): with `n_k` the `k`-th primorial and `1 = a_1 < a_2 < ⋯ < a_{φ(n_k)} = n_k − 1` the integers coprime to `n_k`, estimate the smallest even integer not of the form `a_{i+1} − a_i`, and decide whether there are `≫ max_i (a_{i+1} − a_i)` many even integers of that form.

**Scope statement.** The estimates and the questions themselves are open and are not addressed. The problem page records: "Clearly all differences `a_{i+1} − a_i` are even." This package proves that remark: for `k ≥ 1` the prime `2` divides `n_k`, so every integer coprime to `n_k` is odd and consecutive ones differ by an even number. There is no formal-conjectures statement for #854, so the definitions are ours: `primorialK k` is the product of the first `k` primes (`Nat.nth Nat.Prime`), and `coprimeSeq k` is Mathlib's `Nat.nth` enumeration of the naturals coprime to `n_k`, indexed from `0` (`coprimeSeq k i = a_{i+1}`); this infinite `n_k`-periodic sequence has the page's `a_1, …, a_{φ(n_k)}` as its initial segment, and the evenness of the gaps holds for every index.

## Statement and proof

[Erdos854GapsEven/Main.lean](Erdos854GapsEven/Main.lean) proves

```lean
theorem erdos_854_gap_even (k i : ℕ) (hk : 1 ≤ k) :
    Even (coprimeSeq k (i + 1) - coprimeSeq k i)

theorem erdos_854_gap_even_closed :
    ¬ ∃ k i : ℕ, 1 ≤ k ∧ ¬ Even (coprimeSeq k (i + 1) - coprimeSeq k i)
```

together with `primorialK 1 = 2`, `primorialK 2 = 6`, `primorialK 3 = 30`, the strict monotonicity of the sequence and `a_1 = 1`.

Proof. `2 = nth Prime 0` divides `n_k` for `k ≥ 1`; the set of naturals coprime to `n_k` is infinite (it contains every `1 + n_k t`), so every term of the `Nat.nth` enumeration is coprime to `n_k`, hence odd; the difference of two odd numbers is even.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
