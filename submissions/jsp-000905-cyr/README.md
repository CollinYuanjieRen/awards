# JSP-000905: Erdős #1088 / #503, a six-point planar set with every triangle isosceles

This package submits, for intake and eligibility review, a Lean proof of a settled component of [JSP-000905](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000905) / [Erdős Problem #1088](https://www.erdosproblems.com/1088): let `f_d(n)` be the least `m` such that any `m` points in `ℝ^d` contain `n` points with pairwise distinct distances; estimate `f_d(n)`. The problem page records "Erdős could prove `f_2(3) = 7`", and the case `n = 3` is [Erdős Problem #503](https://www.erdosproblems.com/503): the largest planar set in which every three points form an isosceles triangle has `6` points (Erdős–Kelly 1947, AMM E735).

**Scope statement.** The asymptotic question `f_d(n) = 2^{o(d)}` is open and not addressed. This package proves the construction half only: the vertices of a regular pentagon together with its centre form a six-point set in which every three points form an isosceles triangle, so `6` is attained in #503 (`d = 2`) and `f_2(3) ≥ 7` in #1088. Kelly's matching upper bound (no seven such points; `f_2(3) ≤ 7`), Croft's `d = 3` result, and everything else in #503/#1088 are not claimed.

## Statement and proof

[Erdos503IsoscelesSix/Main.lean](Erdos503IsoscelesSix/Main.lean) copies the formal-conjectures predicates `IsIsosceles`, `Set.Triplewise` and `Set.IsIsosceles` verbatim (from `FormalConjecturesForMathlib/Geometry/2d.lean` and `Data/Set/Triplewise.lean`; `ℝ²` there is `EuclideanSpace ℝ (Fin 2)`) and proves

```lean
theorem erdos_503_R2_six_point_isosceles_set :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)), A.IsIsosceles ∧ A.ncard = 6
```

together with `six_mem_isosceles_ncards : 6 ∈ {(A.ncard) | (A : Set ℝ²) (hA : A.IsIsosceles)}`, the membership half of the [formal-conjectures statement `Erdos503.erdos_503.variants.R2`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/503.lean) (`IsGreatest {…} 6`, open with `sorry`), and the #1088 reading `exists_six_points_no_three_distinct_distances` (six points, no three with pairwise distinct distances).

Proof. With `P_j = (cos 2πj/5, sin 2πj/5)` and `O = (0, 0)`, `dist(P_i, P_j)² = 2 − 2 cos(2π(i − j)/5)` depends only on the cyclic gap, taking one value for gaps `±1, ±4` and another for gaps `±2, ±3`; any three vertices have two equal gaps among their three, and any triple containing `O` has two unit sides. The six points are distinct because these chord lengths are positive (`cos(2πk/5) < 1` for `0 < k < 5`).

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the predicate definitions by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. One `set_option linter.unusedVariables false in` silences the unused-binder lint on the formal-conjectures-shaped corollary; it is a linter option with no semantic effect. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The construction is Erdős's (1946) and Erdős–Kelly's (1947). The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000905-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
