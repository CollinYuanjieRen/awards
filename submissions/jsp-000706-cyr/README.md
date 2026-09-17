# JSP-000706: Erdős #853, every prime gap after the first is even

This package submits, for intake and eligibility review, a Lean proof of the remark on the page of [JSP-000706](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000706) / [Erdős Problem #853](https://www.erdosproblems.com/853): with `d_n = p_{n+1} − p_n`, let `r(x)` be the smallest even `t` such that `d_n = t` has no solution with `n ≤ x`; does `r(x) → ∞`, and does `r(x)/log x → ∞`?

**Scope statement.** The questions about `r(x)` are open and are not addressed. The problem page records: "In [Er85c] Erdős omits the condition that `t` be even, but this is clearly necessary." This package proves that remark with the formal-conjectures definition `primeGap` (from `FormalConjectures/OEIS/92243.lean`, used by the formal-conjectures rendering of `r`) copied verbatim: every gap `primeGap n` with `n ≠ 1` is even (the only odd gap is `3 − 2 = 1`), so no odd `t > 1` is ever a prime gap and the restriction to even `t` is necessary. The theorem statements are ours.

## Statements and proof

[Erdos853GapsEven/Main.lean](Erdos853GapsEven/Main.lean) proves

```lean
theorem primeGap_even (n : ℕ) (hn : n ≠ 1) : Even (primeGap n)
theorem primeGap_ne_odd (t : ℕ) (ht : Odd t) (ht1 : 1 < t) : ¬ ∃ n, primeGap n = t
```

together with a closed form used by our internal audit tooling.

Proof. `nth Prime 0 = 2`; for `n ≥ 2` both `nth Prime n` and `nth Prime (n − 1)` are primes larger than `2` (strict monotonicity of `Nat.nth` on the infinite set of primes), hence odd, and the difference of two odd numbers is even; `primeGap 0 = 2 − 2 = 0`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000706-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
