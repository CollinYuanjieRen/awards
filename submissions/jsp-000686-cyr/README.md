# JSP-000686: Erdős #830, the amicable pair `220, 284`

This package submits, for intake and eligibility review, a Lean verification of the example recorded on the page of [JSP-000686](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000686) / [Erdős Problem #830](https://www.erdosproblems.com/830): `a, b ∈ ℕ` are an amicable pair if `σ(a) = σ(b) = a + b`; are there infinitely many amicable pairs, and does their counting function satisfy `A(x) > x^{1−o(1)}`?

**Scope statement.** Both questions are open and are not addressed, nor are Erdős's and Pomerance's upper bounds on `A(x)`. The problem page records: "For example `220` and `284`." This package verifies that example with the structure `IsAmicable` copied verbatim from formal-conjectures (the definition used by its rendering of #830): `σ(220) = σ(284) = 504 = 220 + 284`.

## Statement and proof

[Erdos830Amicable/Main.lean](Erdos830Amicable/Main.lean) proves

```lean
theorem erdos_830_example : IsAmicable 220 284
theorem erdos_830_example_closed :
    IsAmicable 220 284 ∧ σ 1 220 = 504 ∧ σ 1 284 = 504 ∧ 220 + 284 = 504
```

Proof. `σ 1 n = ∑_{d ∣ n} d`; the divisor sums of `220 = 2²·5·11` and `284 = 2²·71` are both `504`, evaluated by the kernel; `220 ≠ 284`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the example as a typed `example`, checks that `IsAmicable` is the formal-conjectures structure, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
