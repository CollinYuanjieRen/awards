# JSP-000087: Erdős #69, Tao's identity ∑_{n ≥ 2} ω(n)/2^n = ∑_p 1/(2^p − 1)

This package submits, for intake and eligibility review, a Lean proof of the reduction step recorded on the page of [JSP-000087](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000087) / [Erdős Problem #69](https://www.erdosproblems.com/69): is `∑_{n ≥ 2} ω(n)/2^n` irrational, where `ω(n)` is the number of distinct prime divisors of `n`?

**Scope statement.** The irrationality itself (proved unconditionally by Tao and Teräväinen, 2025; formal-conjectures `erdos_69`) is not claimed. The problem page records Tao's observation that the question is a special case of Erdős #257 because `∑_{n ≥ 2} ω(n)/2^n = ∑_p 1/(2^p − 1)`. This package proves exactly that identity, which formal-conjectures states as `erdos_69.variants.specialisation_of_erdos_257` (tagged "research solved" with `sorry`). We note that plby/lean-proofs has published an independent Lean proof of the irrationality of the whole record (by a different route, not via this identity); the catalog entry still records "Lean proof: No".

## Statement and proof

[Erdos69TaoIdentity/Main.lean](Erdos69TaoIdentity/Main.lean) proves, with `ω` being Mathlib's `ArithmeticFunction.cardDistinctFactors`,

```lean
theorem erdos_69_tao_identity :
    ∑' n, ω (n + 2) / (2 ^ (n + 2) : ℝ) = ∑' p : { n : ℕ | n.Prime }, 1 / (2 ^ p.1 - 1)
```

and derives from it the formal-conjectures statement verbatim (with its `let A := { n : ℕ | n.Prime }`):

```lean
theorem Erdos69.erdos_69.variants.specialisation_of_erdos_257 :
    let A := { n : ℕ | n.Prime }
    ∑' n, ω (n + 2) / (2 ^ (n + 2) : ℝ) = ∑' p : A, 1 / (2 ^ p.1 - 1)
```

Proof. Since `ω(n) = ∑_{p ∣ n, p prime} 1`, the left side is the double series `∑_n ∑_p [p prime, p ∣ n] 2^{-n}`, which is absolutely summable (majorant `(3/4)^n (3/4)^p`). Swapping the order, the column of a prime `p` is the geometric series `∑_{m ≥ 1} 2^{-pm} = 1/(2^p − 1)`, and the columns of non-primes vanish; the terms `n = 0, 1` of the row sum vanish because `ω(0) = ω(1) = 0`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the formal-conjectures theorem as a typed `example`, checks that `ω` is Mathlib's arithmetic function by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The identity is Tao's observation as recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000087-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
