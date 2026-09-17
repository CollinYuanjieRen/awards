# JSP-000893: Erdős #1074, the Pillai primes are infinite (Erdős–Hardy–Subbarao)

This package submits, for intake and eligibility review, a Lean proof of the known component of [JSP-000893](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000893) / [Erdős Problem #1074](https://www.erdosproblems.com/1074): a prime `p` is a *Pillai prime* if there is an `m ≥ 1` with `p ≢ 1 (mod m)` and `p ∣ m! + 1`.

**Scope statement.** Erdős's questions, whether the EHS numbers have a density and whether the Pillai primes have a relative density among the primes, are open and are not addressed. The problem page records that Erdős, Hardy and Subbarao proved that both sets are infinite. This package proves that the set of Pillai primes is infinite. The infinitude of the EHS numbers (which formal-conjectures links to an AlphaProof proof) is not claimed.

## Statement and proof

[Erdos1074PillaiPrimes/Main.lean](Erdos1074PillaiPrimes/Main.lean) copies the definitions `EHSNumbers` and `PillaiPrimes` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1074.lean) verbatim and proves

```lean
theorem pillaiPrimes_infinite : PillaiPrimes.Infinite
```

which is exactly the formal-conjectures statement `Erdos1074.erdos_1074.variants.PillaiPrimes_infinite` (tagged "research solved" with `sorry`). The negated form `pillaiPrimes_not_finite : ¬ PillaiPrimes.Finite` (definitionally the same) is also stated for our internal audit tooling.

Proof (Hardy–Subbarao, Amer. Math. Monthly 109 (2002) 554–559, Theorem 2.1, simplified). For every `K` let `n = 10K + 7` and let `p` be the least prime factor of `n! + 1`; then `p > n`. If `p ≢ 1 (mod n)`, then `p` is a Pillai prime with witness `n`. Otherwise `p = 1 + A·n` with `A ≥ 2`; put `m = p − 1 − n`. By Wilson's theorem and `(p − 1)! = m! · (m+1)(m+2)⋯(m+n)` with `m + i ≡ −(n + 1 − i) (mod p)`, we get `−1 ≡ (p−1)! ≡ m! · (−1)^n · n! ≡ m!`, so `p ∣ m! + 1`; and `p ≡ 1 (mod m)` would force `A = 2`, `p = 2n + 1 = 5(4K + 3)`, not prime. So `p` is a Pillai prime with witness `m`. Hence there are Pillai primes above every `K`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definitions by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The theorem and its proof are due to Erdős, Hardy and Subbarao (Hardy–Subbarao 2002), as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000893-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
