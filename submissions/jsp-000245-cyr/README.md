# JSP-000245: Erdős #288, the example `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`

This package submits, for intake and eligibility review, a Lean proof of the example recorded on the page of [JSP-000245](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000245) / [Erdős Problem #288](https://www.erdosproblems.com/288): are there only finitely many pairs of intervals `I₁, I₂` of positive integers such that `∑_{n ∈ I₁} 1/n + ∑_{n ∈ I₂} 1/n` is an integer?

**Scope statement.** The finiteness question is open and is not addressed, nor are its variants. The problem page records: "For example, `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1`." This package verifies that example as membership of the pair of intervals `[3, 6]`, `[20, 20]` in the set of interval pairs whose reciprocal sums total a positive integer, written exactly as in the formal-conjectures statement `Erdos288.erdos_288` (the set expression is copied verbatim under our own name `integralReciprocalPairs`).

## Statement and proof

[Erdos288Example/Main.lean](Erdos288Example/Main.lean) defines

```lean
def integralReciprocalPairs : Set (Fin 2 → ℕ+ × ℕ+) :=
  { I : Fin 2 → ℕ+ × ℕ+ |
    ∀ j, (I j).1 ≤ (I j).2 ∧
      ∃ n : ℕ+, (∑ j : Fin 2, ∑ nⱼ ∈ Set.Icc (I j).1 (I j).2, (nⱼ⁻¹ : ℚ)) = n }
```

and proves

```lean
theorem erdos_288_example :
    (![((3 : ℕ+), (6 : ℕ+)), ((20 : ℕ+), (20 : ℕ+))] : Fin 2 → ℕ+ × ℕ+) ∈ integralReciprocalPairs
```

The closed root `erdos_288_example_closed` packages this membership together with the literal identity `(3 : ℚ)⁻¹ + 4⁻¹ + 5⁻¹ + 6⁻¹ + 20⁻¹ = 1` (`erdos_288_identity`).

Proof. The intervals are `{3, 4, 5, 6}` and `{20}` (by `decide` on `Finset.Icc` in `ℕ+`), the endpoint inequalities hold, and `1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1` by `norm_num`, with witness `n = 1`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example`, checks by `rfl` that the set is the formal-conjectures expression, and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
