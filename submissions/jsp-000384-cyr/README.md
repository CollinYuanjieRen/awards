# JSP-000384: Erdős #472 (Ulam), the example `3, 5, 7, 11, 13, 17, …`

This package submits, for intake and eligibility review, a Lean verification of the example recorded on the page of [JSP-000384](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000384) / [Erdős Problem #472](https://www.erdosproblems.com/472): given an initial finite sequence of primes `q₁ < ⋯ < q_m`, extend it so that `q_{n+1}` is the smallest prime of the form `q_n + q_i − 1`; is there an initial sequence for which the resulting sequence is infinite?

**Scope statement.** Ulam's question is open and is not addressed. The problem page records: "For example if we begin with `3, 5` then the sequence continues `3, 5, 7, 11, 13, 17, …`." This package verifies that example with the rule formalized as a computable function (`ulamNext`, the least prime among `q_n + q_i − 1`, or `0` if there is none, meaning the sequence stops) and proved to satisfy its specification; whether the sequence starting `3, 5` is infinite is not claimed. There is no formal-conjectures statement for #472, so the definitions are ours.

## Statement and proof

[Erdos472Ulam/Main.lean](Erdos472Ulam/Main.lean) defines

```lean
def ulamNext (l : List ℕ) : ℕ :=
  ((l.map fun q => l.getLastD 0 + q - 1).filter fun p => decide (Nat.Prime p)).min?.getD 0
def ulamExtend (init : List ℕ) : ℕ → List ℕ
  | 0 => init
  | k + 1 => ulamExtend init k ++ [ulamNext (ulamExtend init k)]
```

proves the specification lemmas `ulamNext_spec` (a nonzero value is a prime of the form `q_n + q_i − 1`) and `ulamNext_le` (it is the least such prime), and

```lean
theorem erdos_472_example :
    ulamNext [3, 5] = 7 ∧ ulamNext [3, 5, 7] = 11 ∧ ulamNext [3, 5, 7, 11] = 13 ∧
      ulamNext [3, 5, 7, 11, 13] = 17 ∧ ulamExtend [3, 5] 4 = [3, 5, 7, 11, 13, 17]
```

Proof. The values are decided by the kernel (candidates `7, 9` → `7`; `9, 11, 13` → `11`; `13, 15, 17, 21` → `13`; `15, 17, 19, 23, 25` → `17`); the specification lemmas follow from the characterization of `List.min?`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the example as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
