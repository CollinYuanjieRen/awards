# JSP-000329: Erdős #400, the easy bound g_k(n) ≪_k log n

This package submits, for intake and eligibility review, a Lean proof of the known upper bound in [JSP-000329](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000329) / [Erdős Problem #400](https://www.erdosproblems.com/400): for `k ≥ 2` let `g_k(n)` be the maximum of `(a₁ + ⋯ + a_k) − n` over integers with `a₁! ⋯ a_k! ∣ n!`; Erdős and Graham asked whether `∑_{n ≤ x} g_k(n) ∼ c_k x log x` and whether `g_k(n) = c_k log x + o(log x)` for almost all `n < x`.

**Scope statement.** Both asymptotic questions are open. The problem page records that "it is easy to show that `g_k(n) ≪_k log n` always, but the best possible constant is unknown". This package proves that bound with the explicit constant `g_k(n) ≤ k(⌊log₂ n⌋ + 1)`; the asymptotic questions and the best constant are not claimed.

## Statement and proof

[Erdos400LogBound/Main.lean](Erdos400LogBound/Main.lean) copies the definition `g` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/400.lean) verbatim and proves

```lean
theorem g_le (k n : ℕ) : g k n ≤ k * (Nat.log 2 n + 1)
theorem g_isBigO_log (k : ℕ) :
    (fun n : ℕ ↦ (g (k + 2) n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ))
theorem erdos_400_upper_bound (k : ℕ) (hk : k ≥ 2) :
    (fun n : ℕ ↦ (g k n : ℝ)) =O[atTop] (fun n : ℕ ↦ Real.log (n : ℝ))
```

the last being exactly the formal-conjectures statement `Erdos400.erdos_400.variants.upper_bound` (`≪` there is `IsBigO atTop`; tagged "research solved" with `sorry`).

Proof. Compare `2`-adic valuations: by Legendre, `v₂(a!) = a − s₂(a)` with `s₂` the binary digit sum (Mathlib's `Nat.sub_one_mul_padicValNat_factorial`). From `∏ aᵢ! ∣ n!` we get `∑ (aᵢ − s₂(aᵢ)) ≤ n − s₂(n)`, so `∑ aᵢ − n ≤ ∑ s₂(aᵢ) ≤ k(⌊log₂ n⌋ + 1)` since each `aᵢ ≤ n`. As `⌊log₂ n⌋ ≤ log n / log 2`, this gives `g_k(n) ≤ (2k / log 2) log n` for `n ≥ 2`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The bound is the easy one recorded by Erdős and Graham. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000329-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
