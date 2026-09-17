# JSP-000993: Erdős #1188, without minimality there are `≫ 2^x` distinct covering systems

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000993](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000993) / [Erdős Problem #1188](https://www.erdosproblems.com/1188): estimate `F(x)`, the number of minimal distinct covering systems with all moduli in `[1, x]`.

**Scope statement.** The estimate of `F(x)` (and the count of irreducible covering sets) is not addressed. The problem page records that Erdős "asked this without the minimal assumption, but otherwise this is trivial (since e.g. any system containing some fixed covering system would work, resulting in `≫ 2^x` many such systems)". This package proves that remark: the number of distinct covering systems (not necessarily minimal) with moduli in `[1, x]` is at least `2^(x − 6)` for `x ≥ 12`, since adding any set of further moduli (with residue `0`) to the fixed covering system `0 (mod 2), 0 (mod 3), 1 (mod 4), 1 (mod 6), 11 (mod 12)` gives a distinct covering system. The definitions `CongruenceClass`, `ValidClass`, `Satisfies`, `Covers`, `HasDistinctModuli` and `ClassesUpTo` are copied verbatim from the formal-conjectures rendering of #1188; the non-minimal count `distinctCoveringCount` mirrors its `coveringCount` with the minimality clause removed.

## Statement and proof

[Erdos1188CoveringCount/Main.lean](Erdos1188CoveringCount/Main.lean) proves

```lean
theorem erdos_1188_trivial_count (x : ℕ) (hx : 12 ≤ x) : 2 ^ (x - 6) ≤ distinctCoveringCount x
theorem erdos_1188_trivial_count_closed :
    ¬ ∃ x : ℕ, 12 ≤ x ∧ distinctCoveringCount x < 2 ^ (x - 6)
```

Proof. The base system covers `ℤ` (check residues modulo `12`); for each subset `T` of the `x − 6` moduli in `[2, x] ∖ {2, 3, 4, 6, 12}`, the system `base ∪ {0 (mod n) : n ∈ T}` is a valid distinct covering system with moduli in `[1, x]`, and different `T` give different systems; hence the count is at least `2^(x − 6)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks that the covering-system definitions are the formal-conjectures ones, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
