# JSP-000749: Erdős's lower bound 2^{n−1} ≤ m(n) and m(2) = 3 (scoped component of Erdős #901)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000749](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000749) (Erdős Problem [#901](https://www.erdosproblems.com/901)): let `m(n)` be the least number of edges of an `n`-uniform `3`-chromatic hypergraph (one without *Property B*); estimate `m(n)`.

**Estimating `m(n)` is open.** This package formalizes the classical **lower bound** `2^{n−1} ≤ m(n)` (Erdős: every `n`-uniform hypergraph with fewer than `2^{n−1}` edges is `2`-colourable, by a union-bound counting of colourings) and the exact value **`m(2) = 3`** (the triangle `{01, 12, 02}`).

## Statement and proof

`MerLeanExperiment/Defs.lean` fixes the definitions: `IsUniform n E` (every edge has exactly `n` vertices); `TwoColorable E := ∃ c : V → Bool, ∀ e ∈ E, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v` (Property B: some 2-colouring makes every edge bichromatic); and

```lean
noncomputable def m (n : ℕ) : ℕ :=
  sInf {k | ∃ (N : ℕ) (E : Finset (Finset (Fin N))), IsUniform n E ∧ ¬ TwoColorable E ∧ E.card = k}
```

The package proves (`MerLeanExperiment/Main.lean`)

```lean
theorem two_pow_le_m (n : ℕ) : 2 ^ (n - 1) ≤ m n
theorem m_two : m 2 = 3
```

For the lower bound: any `n`-uniform hypergraph with `< 2^{n−1}` edges is `2`-colourable — a uniformly random `2`-colouring makes a fixed `n`-edge monochromatic with probability `2^{1−n}`, so with fewer than `2^{n−1}` edges the expected number of monochromatic edges is `< 1`, hence some colouring has none (a counting/averaging argument, formalized directly). For `m(2) = 3`: the triangle is `2`-uniform and not `2`-colourable, and any `2`-uniform hypergraph with `≤ 2` edges is `2`-colourable.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and the two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/901) is recorded verbatim in `sources/erdos901-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of `two_pow_le_m` and `m_two`: `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry`s are the two statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution and submission status

The lower bound is Erdős's classical counting argument [ErLo75]. This scoped component (lower bound + `m(2)`) is distinct from the separate upstream evidence submission on the upper-bound side. The formalization was authored independently (own definitions; no third-party Lean source copied), with Claude (Anthropic) assistance and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000749-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
