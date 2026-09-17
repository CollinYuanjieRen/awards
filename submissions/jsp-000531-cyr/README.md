# JSP-000531: Erdős #655, every point of a valid configuration determines at least (n − 1)/2 distances

This package submits, for intake and eligibility review, a Lean proof of the elementary remark on the page of [JSP-000531](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000531) / [Erdős Problem #655](https://www.erdosproblems.com/655): if `x₁, …, xₙ ∈ ℝ²` are such that no circle centred at one of the `xᵢ` contains three other points, are there at least `(1 + c)·n/2` distinct distances?

**Scope statement.** The main question (disproved as stated by Zach Hunter's regular n-gon, for which formal-conjectures links an external formal proof) and its open general-position variant are not addressed. The problem page records: "It is easy to see that this assumption implies that there are at least `(n − 1)/2` distinct distances determined by every point." This package proves exactly that remark, with the formal-conjectures definitions `IsValid` (from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/655.lean), with `ℝ²` written as `EuclideanSpace ℝ (Fin 2)`) and `distinctDistancesFrom` (`FormalConjecturesForMathlib/Geometry/Metric.lean`) copied verbatim; the theorem statement is ours.

## Statement and proof

[Erdos655PerPoint/Main.lean](Erdos655PerPoint/Main.lean) proves

```lean
theorem erdos_655_distinctDistancesFrom (X : Finset (EuclideanSpace ℝ (Fin 2))) (hX : IsValid X)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ X) : #X - 1 ≤ 2 * distinctDistancesFrom X x
```

together with a closed form used by our internal audit tooling.

Proof. The map `y ↦ dist y x` sends the `n − 1` other points onto the set of distances from `x`; the fibre over a distance `r > 0` is `X ∩ sphere x r`, which has at most two points by validity, so `n − 1 ≤ 2 · (number of distinct distances from x)` (Mathlib's `Finset.card_le_mul_card_image`).

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definitions by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The remark is the elementary observation recorded on the problem page. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000531-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
