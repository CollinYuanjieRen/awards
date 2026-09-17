# JSP-001012: Erdős #1207, `P_d(n) ≥ f_d(n)`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-001012](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-1001-1022.md#JSP-001012) / [Erdős Problem #1207](https://www.erdosproblems.com/1207): let `P_d(n)` be such that any set of `n` points in `ℝ^d` contains at least `P_d(n)` points with no isosceles triangle; estimate `P_d(n)`, in particular is `P_2(n) < n^{1 − c}`?

**Scope statement.** The estimates are open and are not addressed, nor are the lower bounds `n^{1/(3d−3) − o(1)}`, `n^{0.432}` or the upper bound `n^{1/2}` quoted on the page. The problem page records: "Indeed, one can take any subset of points with all distinct distances, whence `P_d(n) ≥ f_d(n)`", where `f_d(n)` (Erdős #1208) is the largest number such that any `n` points in `ℝ^d` contain `f_d(n)` points with all pairwise distances distinct. This package proves that inequality. The definitions `Set.Triplewise`, `IsIsosceles`, `Set.IsIsoscelesFree`, the notation `ℝ^d` and `Erdos1207.P` are copied verbatim from formal-conjectures; there is no formal-conjectures statement for `f_d(n)`, so `IsDistinctDistances` and `f` are ours, mirroring `P`.

## Statement and proof

[Erdos1207IsoscelesFree/Main.lean](Erdos1207IsoscelesFree/Main.lean) proves

```lean
theorem isIsoscelesFree_of_isDistinctDistances {α : Type*} [Dist α] (A : Set α)
    (h : IsDistinctDistances A) : A.IsIsoscelesFree
theorem erdos_1207_f_le_P (d n : ℕ) : f d n ≤ P d n
theorem erdos_1207_f_le_P_closed : ¬ ∃ d n : ℕ, P d n < f d n
```

Proof. In a set with all distinct distances, three distinct points cannot form an isosceles triangle (two of its sides are distinct pairs with equal length); so for every point set the largest distinct-distance subset is at most the largest isosceles-free subset, and taking the minimum over all `n`-point sets gives `f_d(n) ≤ P_d(n)`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
