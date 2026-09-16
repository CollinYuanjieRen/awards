# JSP-000736: Erdős #885, common factor differences for k = 2 and k = 3

This package submits, for intake and eligibility review, Lean proofs of the known cases of [JSP-000736](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000736) / [Erdős Problem #885](https://www.erdosproblems.com/885): for `n ≥ 1` let `D(n) = {|a − b| : n = ab}`; is it true that for every `k ≥ 1` there are integers `N₁ < ⋯ < N_k` with `|⋂ D(Nᵢ)| ≥ k`?

**Scope statement.** The general question is open. The problem page records that Erdős and Rosenfeld (1997) proved the case `k = 2`, Jiménez-Urroz (1999) the case `k = 3`, and Bremner (2019) the case `k = 4`. This package proves the cases `k = 2` and `k = 3` by explicit certificates; the case `k = 4` and the general question are not claimed.

## Statement and proof

[Erdos885KnownCases/Main.lean](Erdos885KnownCases/Main.lean) copies the definition `factorDifferenceSet` of the [formal-conjectures file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/885.lean) verbatim and proves `erdos_885_k_eq_2` and `erdos_885_k_eq_3`, which are exactly the statements `Erdos885.erdos_885.variants.k_eq_2` and `k_eq_3` there (tagged "research solved" with `sorry`), together with their conjunction `erdos_885_k_two_and_three`:

```lean
theorem erdos_885_k_eq_3 :
    ∃ Ns : Finset ℕ, (∀ n ∈ Ns, 1 ≤ n) ∧ Ns.card = 3 ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ 3
```

Certificates: `D(12) ∩ D(42) ⊇ {1, 11}` (`12 = 3·4 = 1·12`, `42 = 6·7 = 3·14`) and `D(112) ∩ D(952) ∩ D(3240) ⊇ {6, 54, 111}` (`112 = 8·14 = 2·56 = 1·112`, `952 = 28·34 = 14·68 = 8·119`, `3240 = 54·60 = 36·90 = 24·135`); the factor-difference sets are finite (contained in `[0, n]`), so the cardinality bounds follow from these inclusions.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorems as typed `example`s, checks the definition by `rfl`, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.

## Attribution and submission status

The results are Erdős–Rosenfeld's (`k = 2`) and Jiménez-Urroz's (`k = 3`); the certificates used here were found by exhaustive search. The Lean proof was prepared with Claude Code (Claude Fable 5.1 orchestration, Claude Opus 5 implementation) assistance. No mathematical novelty and no entitlement to an award is claimed; please assess whether this component contributes eligible formalization work for the record.

Proposed formalizer: `RECIPIENT-jsp-000736-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging. This is a self-submission with a direct interest in the review outcome. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
