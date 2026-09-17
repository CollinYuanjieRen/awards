# JSP-000325: Erdős #394, the trivial lower bound Σ_{n ≤ x} t₂(n) ≫ x²/log x

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000325](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000325) / [Erdős Problem #394](https://www.erdosproblems.com/394): let `t_k(n)` be the least `m ≥ 1` such that `n ∣ m(m+1)⋯(m+k−1)`; Erdős and Graham asked about the average behaviour of `t_k`.

**Scope statement.** The questions on the problem page are open. The page records: "since `t₂(p) = p − 1` for prime `p` it is trivial that `∑_{n ≤ x} t₂(n) ≫ x²/log x`." This package proves exactly that bound; the open questions and Hall's bound are not claimed.

## Statement and proof

[Erdos394LowerBound/Main.lean](Erdos394LowerBound/Main.lean) copies the definition `t` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/394.lean) verbatim and proves `t_two_prime : p.Prime → t 2 p = p − 1` and

```lean
theorem erdos_394_lower_bound :
    Asymptotics.IsBigO Filter.atTop ((fun x ↦ x ^ 2 / Real.log x) : ℕ → ℝ)
      ((fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, (t 2 n : ℝ)) : ℕ → ℝ)
```

which is exactly the formal-conjectures statement `Erdos394.erdos_394.variants.lower_bound` (there written with the notation `≪`, meaning `IsBigO atTop` on functions `ℕ → ℝ`; tagged "research solved" with `sorry`).

Proof. If a prime `p` divides `n` then `t₂(n) ≥ p − 1` (since `p ∣ m(m+1)` forces `m + 1 ≥ p`). No `n ≤ x` has two distinct prime factors exceeding `√x`, so summing `p − 1` over the primes `√x < p ≤ x/2` dividing `n` gives at most `t₂(n)`; summing over `n ≤ x` and swapping the order, each such prime contributes `(p − 1)⌊x/p⌋ ≥ x/4`, which yields `x·π(x/2) ≤ 4 ∑_{n ≤ x} t₂(n) + x√x` for `x ≥ 16`. Mathlib's Chebyshev lower bound for `π` then gives `x²/log x ≤ 20 ∑_{n ≤ x} t₂(n)` for all `x ≥ 10⁸`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the trivial one recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000325-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
