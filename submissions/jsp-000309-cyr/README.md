# JSP-000309: Erdős #374, no D_k contains a prime

This package submits, for intake and eligibility review, a Lean proof of one of the known facts listed on the page of [JSP-000309](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000309) / [Erdős Problem #374](https://www.erdosproblems.com/374): for `m ∈ ℕ` let `F(m)` be the minimal `k ≥ 2` (if it exists) such that there are `a₁ < ⋯ < a_k = m` with `a₁! ⋯ a_k!` a square, and let `D_k = {m : F(m) = k}`; Erdős and Graham asked for the growth of `|D_k ∩ {1, …, n}|` for `3 ≤ k ≤ 6`.

**Scope statement.** The growth questions and the other listed facts (`D_2 = {n² : n > 1}`, the `D_3`/`D_4` comparison, the least element of `D_6`, `D_k = ∅` for `k > 6`) are not addressed. The problem page records: "no `D_k` contains a prime". This package proves exactly that. Formal-conjectures has no file for #374, so the definitions are ours: a set `a₁ < ⋯ < a_k = m` is a finset `s` with `m ∈ s` and all elements `≤ m`, `k = #s`; `F m` is the least such `k ≥ 2`; `D k` is the set of `m` admitting such a finset of size `k` with `F m = k`.

## Statements and proof

[Erdos374NoPrime/Main.lean](Erdos374NoPrime/Main.lean) proves

```lean
theorem not_isFactorialSquareSet_of_prime (p : ℕ) (hp : p.Prime) (s : Finset ℕ) :
    ¬ IsFactorialSquareSet p s
theorem erdos_374_prime_notMem_D (p k : ℕ) (hp : p.Prime) : p ∉ D k
```

together with a closed form used by our internal audit tooling.

Proof. If the largest element `p` is prime then `p` divides `p!` exactly once and does not divide `a!` for `a < p`, so the exponent of `p` in `a₁! ⋯ a_k!` is `1`, which is odd; a square has even exponents. Hence no factorial-square set ends at a prime, and no prime lies in any `D_k`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, unfolds the definitions by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The fact is one recorded on the problem page (Erdős–Graham 1976). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000309-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
