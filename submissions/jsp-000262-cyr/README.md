# JSP-000262: Erdős #313, the denominator of a solution is the product of its primes

This package submits, for intake and eligibility review, a Lean proof of the elementary structural remark on the page of [JSP-000262](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000262) / [Erdős Problem #313](https://www.erdosproblems.com/313): are there infinitely many solutions of `1/p₁ + ⋯ + 1/p_k = 1 − 1/m` with `m ≥ 2` an integer and `p₁ < ⋯ < p_k` distinct primes?

**Scope statement.** The infinitude question is open and is not addressed. The problem page records: "It is clear that we must have `m = p₁ ⋯ p_k`, and hence in particular there is at most one solution for each `m`." This package proves exactly that, for the formal-conjectures solution set `Erdos313.erdos313Solutions` (copied verbatim; formal-conjectures states no theorem for this remark, so the theorem statements are ours).

## Statements and proof

[Erdos313Structure/Main.lean](Erdos313Structure/Main.lean) proves

```lean
theorem erdos313_denominator_eq_prod {m : ℕ} {P : Finset ℕ} (h : (m, P) ∈ erdos313Solutions) :
    m = ∏ p ∈ P, p

theorem erdos313_unique {m : ℕ} {P Q : Finset ℕ} (hP : (m, P) ∈ erdos313Solutions)
    (hQ : (m, Q) ∈ erdos313Solutions) : P = Q
```

together with a closed combined form used by our internal audit tooling.

Proof. Put `N = ∏_{p ∈ P} p` and `S = ∑_{p ∈ P} N/p`; clearing denominators in `∑ 1/p = 1 − 1/m` gives `S·m + N = N·m` in `ℕ`. For each `p ∈ P`, `p ∤ S` (every term but `N/p` is divisible by `p`, and `N/p` is a product of primes different from `p`), so `N` and `S` are coprime; hence `N ∣ m` from `N ∣ S·m`, and `m ∣ N` from `(N − S)·m = N`, so `m = N`. Uniqueness follows since `P` is the set of prime factors of `m` (Mathlib's `Nat.primeFactors_prod`).

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the elementary observation recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000262-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
