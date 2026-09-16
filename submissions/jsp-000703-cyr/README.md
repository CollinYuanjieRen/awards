# JSP-000703: Erdős's two-consecutive family and Makowski's pair (scoped component of Erdős #850)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000703](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000703) (Erdős Problem [#850](https://www.erdosproblems.com/850), the Erdős–Woods question): "Can there exist two distinct integers `x` and `y` such that `x, y` have the same prime factors, `x+1, y+1` have the same prime factors, and `x+2, y+2` also have the same prime factors?"

**The three-consecutive question is open and is not claimed here.** The problem page records the published partial results for the two-consecutive case: Erdős's infinite family `x = 2(2^r − 1)`, `y = x(x+2)` (also Problem 1 of the 3rd Benelux Mathematical Olympiad, 2011) and Makowski's other example `x = 75`, `y = 1215` (A. Makowski, *On a problem of Erdős*, Enseign. Math. (2) 14 (1968), 193). This package formalizes exactly those two statements.

## Statement and proof

`Jsp703/Component.lean` defines

```lean
def TwoConsecutiveExample (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x ≠ y ∧ x.primeFactors = y.primeFactors ∧
    (x + 1).primeFactors = (y + 1).primeFactors
```

with Mathlib's `Nat.primeFactors` (the set of prime divisors), and proves

```lean
theorem erdos_family (r : ℕ) (hr : 1 ≤ r) : TwoConsecutiveExample (erdosX r) (erdosY r)
theorem infinite_twoConsecutive : Set.Infinite {p : ℕ × ℕ | TwoConsecutiveExample p.1 p.2}
theorem makowski_example : TwoConsecutiveExample 75 1215
theorem makowski_not_in_family : ∀ r : ℕ, ¬ (erdosX r = 75 ∧ erdosY r = 1215)
```

where `erdosX r = 2 * (2 ^ r - 1)` and `erdosY r = erdosX r * (erdosX r + 2)`. The proof is the published one: `x + 2 = 2^{r+1}` so `y` has the same prime support as `x`, and `y + 1 = (x + 1)^2`; Makowski's pair is checked from `75 = 3·5²`, `1215 = 3⁵·5`, `76 = 2²·19`, `1216 = 2⁶·19`. The last theorem records that Makowski's pair is not a member of Erdős's family (`erdosX r` is even). Nothing else is asserted: no claim is made about the three-consecutive question, about the finiteness of examples, or about Shorey–Tijdeman's conditional result.

`Challenge.lean` is a comparator-style challenge module (Mathlib-only definitions and the two main targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/850, retrieved 2026-09-16) is recorded verbatim in `sources/erdos850-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the four theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur. `verification.txt` records the local build and audit of this exported package. Local verification used arm64 macOS and cached upstream dependencies; authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The mathematics is Erdős's (the family) and Makowski's (the pair); the contribution sought is formalization of these published partial results, following the fleet convention for scoped components of open problems. The formalization was prepared with Claude (Anthropic) assistance (design and hints by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000703-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
