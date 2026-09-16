# JSP-000773: the two explicit examples of Erdős #931 (scoped component)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000773](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000773) (Erdős Problem [#931](https://www.erdosproblems.com/931)): "Let `k₁ ≥ k₂ ≥ 3`. Are there only finitely many `n₂ ≥ n₁ + k₁` such that `∏_{1≤i≤k₁}(n₁+i)` and `∏_{1≤j≤k₂}(n₂+j)` have the same prime factors?"

**The finiteness question is open and is not claimed here.** The problem page records exactly two explicit facts, and this package formalizes exactly those two, as certificates: Tijdeman's example that `19·20·21·22` and `54·55·56·57` have the same prime factors, and AlphaProof's example `10! = 2⁸·3⁴·5²·7`, `14·15·16 = 2⁵·3·5·7` (`n₁ = 0, k₁ = 10, n₂ = 13, k₂ = 3`), which shows that Erdős's guess "if the two products have the same prime factors then `n₂ > 2(n₁ + k₁)`" is false as literally stated (`13 ≤ 20`). This is a small package of certificate checks; no mathematical discovery is claimed.

## Statement and proof

`Jsp773/Examples.lean` defines, with Mathlib's `Nat.primeFactors`,

```lean
def consProd (n k : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 k, (n + i)
def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  (consProd n₁ k₁).primeFactors = (consProd n₂ k₂).primeFactors
```

and proves

```lean
theorem tijdeman : SamePrimeFactors 18 4 53 4 ∧ 3 ≤ 4 ∧ 18 + 4 ≤ 53
theorem alphaproof : SamePrimeFactors 0 10 13 3 ∧ 3 ≤ 3 ∧ 3 ≤ 10 ∧ 0 + 10 ≤ 13 ∧ 13 ≤ 2 * (0 + 10)
theorem erdos_guess_false :
    ¬ ∀ n₁ k₁ n₂ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ → n₁ + k₁ ≤ n₂ → SamePrimeFactors n₁ k₁ n₂ k₂ → 2 * (n₁ + k₁) < n₂
```

together with the explicit prime-factor sets (`{2, 3, 5, 7, 11, 19}` for both of Tijdeman's products, `{2, 3, 5, 7}` for both of AlphaProof's) and the identities `consProd 18 4 = 19·20·21·22`, `consProd 53 4 = 54·55·56·57`, `consProd 0 10 = 10!`, `consProd 13 3 = 14·15·16`. All checks are kernel-verified computations on concrete integers.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and the three targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/931, retrieved 2026-09-16) is recorded verbatim in `sources/erdos931-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp773/`, `Jsp773.lean`, `Audit.lean`); the only `sorry`s in the package are the three statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package. Local verification used arm64 macOS and cached upstream dependencies; authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The examples are Tijdeman's (as reported by Erdős [Er76d]) and AlphaProof's (as recorded on the problem page); the contribution sought is only their formal certification, following the fleet convention for scoped components of open problems. The formalization was prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000773-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
