# JSP-000219: Erdős #251, the example `g_n = p_n + 1`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000219](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000219) / [Erdős Problem #251](https://www.erdosproblems.com/251): is `∑ p_n / 2^n` irrational?

**Scope statement.** The irrationality questions are open and are not addressed. The page records Erdős's further conjecture that if `g_n ≥ 2` and `g_n = o(p_n)` then `∑ p_n / (g_1 ⋯ g_n)` is irrational, and: "The example `g_n = p_n + 1` shows that some condition on the growth of the `g_n` is necessary here." This package proves that example: with `g_n = p_n + 1` (so `g_n ≥ 2` holds but `g_n = o(p_n)` fails) the series telescopes and sums to `1`, which is rational. The primes are indexed from `0` as in the formal-conjectures statement `Erdos251.erdos_251` (`Nat.nth Nat.Prime`), the sum is taken in `ℝ`, and the statement is ours (formal-conjectures has no statement for the example).

## Statement and proof

[Erdos251Telescoping/Main.lean](Erdos251Telescoping/Main.lean) proves

```lean
theorem erdos_251_example_closed :
    HasSum (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ) /
        ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1)) 1 ∧
      ¬ Irrational (∑' n : ℕ, (Nat.nth Nat.Prime n : ℝ) /
        ∏ i ∈ Finset.range (n + 1), ((Nat.nth Nat.Prime i : ℝ) + 1))
```

together with the telescoping identity `∑_{n < N} p_n / (g_1 ⋯ g_n) = 1 − 1 / (g_1 ⋯ g_{N−1})`, the bound `2^N ≤ g_1 ⋯ g_N`, and `g_n ≥ 2`.

Proof. `p_n / (g_1 ⋯ g_n) = 1/(g_1 ⋯ g_{n−1}) − 1/(g_1 ⋯ g_n)` since `g_n = p_n + 1`, so the partial sums are `1 − 1/(g_1 ⋯ g_N)`, and the products grow at least like `2^N`; hence the series has sum `1`, which is not irrational.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the sum as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
