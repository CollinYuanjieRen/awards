# JSP-000197: Erdős #213, the Kreisel–Kurz integral heptagon in general position

This package submits, for intake and eligibility review, a Lean certificate for the best known construction in [JSP-000197](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000197) / [Erdős Problem #213](https://www.erdosproblems.com/213): for `n ≥ 4`, are there `n` points in the plane, no three on a line and no four on a circle, with all pairwise distances integers?

**Scope statement.** The problem is open for `n ≥ 8`. The problem page records that the best construction to date, due to Kreisel and Kurz (2008), has `n = 7`. This package certifies that construction only. The Anning–Erdős finiteness theorem and the upper bounds of Ascher–Braune–Turchet and Greenfeld–Iliopoulou–Peluse are not addressed, and nothing is claimed for `n ≥ 8`.

## Statement and proof

[Erdos213Heptagon/Main.lean](Erdos213Heptagon/Main.lean) copies the formal-conjectures predicates `Erdos213For`, `NonTrilinear` and `Set.Triplewise` verbatim (from `ErdosProblems/213.lean`, `Geometry/2d.lean` and `Data/Set/Triplewise.lean`; `ℝ²` there is `EuclideanSpace ℝ (Fin 2)`) and proves

```lean
theorem erdos_213_KK08 : Erdos213For 7
```

which is exactly the [formal-conjectures statement `Erdos213.erdos_213.variants.KK08`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/213.lean) (tagged "research solved" there with a `sorry`).

The seven points are `(xᵢ, yᵢ √2002)` with the rational `xᵢ, yᵢ` of Kreisel–Kurz (arXiv:0804.1303, Fig. 1, characteristic 2002). After clearing the common denominator `2227`, all three certificate conditions become integer facts decided by the kernel: the `21` squared distances are perfect squares (`kk_dist`), the `35` collinearity determinants are nonzero (`kk_not_collinear`, via the lemma that three collinear points have vanishing determinant), and the `35` concyclicity determinants are nonzero (`kk_not_cospherical`, via the lemma that four cospherical points have vanishing `4 × 4` determinant `det [|p|², x, y, 1]`). The points are distinct because their distances are positive, so the set has `7` elements.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the predicate definition by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`; two `set_option maxRecDepth` settings are resource limits for the kernel `decide` checks). [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The construction is Kreisel and Kurz's (Discrete Comput. Geom. 39 (2008), 786–790). The Lean certificate was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000197-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
