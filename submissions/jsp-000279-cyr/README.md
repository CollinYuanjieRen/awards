# JSP-000279: Erdős #336, the basis `A = ⋃ (2^{2k}, 2^{2k+1}]` has order `2` but exact order `3`

This package submits, for intake and eligibility review, a Lean proof of the example recorded on the page of [JSP-000279](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000279) / [Erdős Problem #336](https://www.erdosproblems.com/336): for `r ≥ 2`, `h(r)` is the maximal finite `k` such that some basis `A ⊆ ℕ` of order `r` (every large integer is the sum of at most `r` integers from `A`) has exact order `k` (every large integer is the sum of exactly `k` integers from `A`); find `lim h(r)/r²`.

**Scope statement.** The limit, the Erdős–Graham criterion for the existence of an exact order, the bounds on the limit and the values of `h` are not addressed. The problem page records: "A simple example of the order of a basis differing from the exact order is given by `A = ⋃_{k ≥ 0} (2^{2k}, 2^{2k+1}]`, which has order `2` but exact order `3`." This package proves that example. There is no formal-conjectures statement for #336, so the definitions are ours: sums of "`k` integers from `A`" allow repetition (lists of elements of `A`), the order of `A` is the least `r` such that every large integer is a sum of at most `r` elements, and the exact order the least `k` such that every large integer is a sum of exactly `k` elements (both as `sInf`).

## Statement and proof

[Erdos336OrderExample/Main.lean](Erdos336OrderExample/Main.lean) defines `A336`, `IsSumOfExactly`, `IsSumOfAtMost`, `IsBasisOfOrderLE`, `IsExactBasisOfOrder`, `basisOrder` and `exactOrder`, and proves

```lean
theorem erdos_336_example : basisOrder A336 = 2 ∧ exactOrder A336 = 3
```

via: sums of exactly two elements cover `[4^j + 3, 4^{j+1}]` for every `j ≥ 1`, while `4^j + 1` and `4^j + 2` are never sums of two elements; every `n ≥ 5` is a sum of at most two elements but infinitely many integers (`2·4^j + 1`) are not in `A`, so the order is `2`; every `n ≥ 20` is a sum of exactly three elements, while infinitely many integers (`4^j + 1`) are not sums of exactly two (nor of exactly one or zero), so the exact order is `3`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
