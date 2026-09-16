# JSP-000234: Erdős #273, Selfridge's covering system with moduli p − 1 (p ≥ 3 prime)

This package submits, for intake and eligibility review, a Lean certificate for the settled variant of [JSP-000234](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000234) / [Erdős Problem #273](https://www.erdosproblems.com/273): is there a covering system of the integers all of whose moduli are of the form `p − 1` for primes `p ≥ 5`?

**Scope statement.** The question for `p ≥ 5` is open and is not addressed. The problem page records that Selfridge found an example using divisors of `360` if `p = 3` is allowed. This package certifies such a system: the twelve congruence classes `(modulus, residue)` = `(2,0), (4,1), (6,3), (10,7), (12,11), (18,1), (30,1), (36,7), (40,23), (60,19), (72,67), (180,175)`, whose moduli `p − 1` come from the primes `3, 5, 7, 11, 13, 19, 31, 37, 41, 61, 73, 181`, are pairwise distinct and cover every residue modulo `360`.

## Statement and proof

[Erdos273Selfridge/Main.lean](Erdos273Selfridge/Main.lean) copies the structures `CoveringSystem` and `StrictCoveringSystem` verbatim from the formal-conjectures repository (`FormalConjecturesForMathlib/NumberTheory/CoveringSystem.lean`: a finite family of residues and ideal moduli whose cosets cover the semiring, with nonzero proper and pairwise distinct moduli) and proves

```lean
theorem erdos_273_three :
    ∃ c : StrictCoveringSystem ℕ, ∀ i, ∃ p, p.Prime ∧ 3 ≤ p ∧ c.moduli i = Ideal.span {↑(p - 1)}
```

which is the `answer(True)` content of the [formal-conjectures statement `Erdos273.erdos_273.variants.three`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/273.lean) (tagged "research solved" with `sorry`). The covering property is a kernel `decide` over the residues modulo `360` (all moduli divide `360`); the moduli are nonzero and proper ideals of `ℕ` and pairwise distinct because the twelve moduli are; primality of the twelve primes is by `norm_num`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`; one scoped `set_option maxRecDepth` is a resource setting for a kernel `decide`). [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The existence of such a system is attributed on the problem page to Selfridge; the particular twelve classes used here were found by exhaustive search over the admissible moduli dividing `360`. The Lean certificate was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000234-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
