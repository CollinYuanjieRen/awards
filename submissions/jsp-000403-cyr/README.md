# JSP-000403: Erdős #503, isosceles sets of C(d+1, 2) + 1 points in ℝ^d (Alweiss, Weisenberg)

This package submits, for intake and eligibility review, a Lean proof of the known lower bound in [JSP-000403](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000403) / [Erdős Problem #503](https://www.erdosproblems.com/503): what is the largest `A ⊆ ℝ^d` such that every three points of `A` form an isosceles triangle?

**Scope statement.** The general question is open (the answer is `6` for `d = 2` by Kelly and `8` for `d = 3` by Croft; Blokhuis proved `|A| ≤ C(d+2, 2)`). The problem page records Alweiss's lower bound `C(d+1, 2)`, from the vectors `eᵢ + eⱼ` (`i < j`) in `ℝ^{d+1}`, which lie in a hyperplane and hence in some `ℝ^d`, and Weisenberg's observation that one further point can be added, giving `C(d+1, 2) + 1`. This package proves that construction for every `d`; the upper bounds and the general question are not claimed.

## Statement and proof

[Erdos503IsoscelesLower/Main.lean](Erdos503IsoscelesLower/Main.lean) copies the formal-conjectures predicates `IsIsosceles`, `Set.Triplewise` and `Set.IsIsosceles` verbatim and proves

```lean
theorem erdos_503_lower_bound_explicit (d : ℕ) :
    ∃ A : Set (EuclideanSpace ℝ (Fin d)), A.IsIsosceles ∧ A.ncard = (d + 1).choose 2 + 1
```

The [formal-conjectures statement `erdos_503.variants.lower_bound`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/503.lean) is phrased as `(n + 1).choose 2 ≤ sSup {A.ncard | A.IsIsosceles}`; over `ℕ` that supremum is only meaningful given an upper bound for isosceles sets (Blokhuis's theorem), so this package proves the explicit existence statement behind it, from which the `sSup` form follows whenever such a bound is available.

Proof. In `ℝ^{d+1}` the points `eᵢ + eⱼ` (`i < j`) have squared distance `2` when the index pairs share an element and `4` otherwise, and the point `(2/(d+1))·(1, …, 1)` is equidistant from all of them; a triangle whose side lengths come from a two-element set is isosceles. All points lie in the affine hyperplane `∑ xᵢ = 2`, which is isometric to `ℝ^d` (an orthonormal basis of the kernel of the coordinate-sum functional), so the configuration transports to `ℝ^d` with the same cardinality. For `d = 1` the extra point coincides with `e₀ + e₁`, so the cases `d ≤ 1` (one point in `ℝ⁰`, two points in `ℝ¹`) are treated directly.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the predicate definition by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The construction is Alweiss's, with Weisenberg's addition (both recorded on the problem page). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record. (Our separate submission for JSP-000905 covers the six-point instance of this problem in the plane.)

Proposed formalizer: `RECIPIENT-jsp-000403-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
