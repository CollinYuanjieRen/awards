# JSP-000142: Erdős #138, existence of the van der Waerden numbers (van der Waerden's theorem)

This package submits, for intake and eligibility review, a Lean proof of the existence component of [JSP-000142](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000142) / [Erdős Problem #138](https://www.erdosproblems.com/138): the van der Waerden number `W(k)` is the least `N` such that every `2`-colouring of `{1, …, N}` contains a monochromatic `k`-term arithmetic progression, and Erdős asks for better bounds on `W(k)`.

**Scope statement.** No bound on `W(k)` is claimed: not Berlekamp's `W(p+1) ≥ p·2^p`, not Gowers's upper bound, not Kozik–Shabanov's `W(k) ≫ 2^k`, not DeepMind's `W(k+1) ≥ W(k) + k`, and not the open question `W(k)^{1/k} → ∞`. The formal-conjectures rendering defines `W` as the infimum of the set of all `N` that force a monochromatic progression and leaves the nonemptiness of that set, for every number of colours `r` and every length `k`, as a `sorry` tagged "research solved". This package proves exactly that statement, which is van der Waerden's theorem (1927), the existence result underlying the definition of `W(k)`. We flag for the reviewer that this is a textbook theorem rather than a result stated as new on the problem page.

## Statement and proof

[Erdos138VdWExists/Main.lean](Erdos138VdWExists/Main.lean) copies the definitions `Set.IsAPOfLengthWith`, `Set.IsAPOfLength`, `ContainsMonoAPofLength` (formal-conjectures `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`) and `Erdos138.monoAP_guarantee_set` from the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/138.lean) verbatim and proves

```lean
theorem monoAP_guarantee_set_nonempty (r k : ℕ) : (monoAP_guarantee_set r k).Nonempty
```

which is exactly the formal-conjectures statement `Erdos138.monoAP_guarantee_set_nonempty`.

Proof. Mathlib's Hales–Jewett theorem (`Combinatorics.Line.exists_mono_in_high_dimension`) gives a finite index type `ι` such that every `r`-colouring of the cube `ι → Fin k` has a monochromatic combinatorial line. With `N = k·|ι| + 1`, colour `v : ι → Fin k` by the colour of `1 + ∑ᵢ vᵢ ∈ {1, …, N}`. A monochromatic line with `s ≥ 1` free coordinates and fixed-part sum `b` yields the monochromatic progression `1 + b + n·s`, `n < k`, of length `k` and difference `s`. The case `k = 0` uses `N = 1` and the empty progression.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks the definitions by `Iff.rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The theorem is van der Waerden's; the proof route through Hales–Jewett follows Mathlib's `Combinatorics.exists_mono_homothetic_copy`. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000142-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
