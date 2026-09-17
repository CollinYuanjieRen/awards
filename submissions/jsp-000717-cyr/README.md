# JSP-000717: Erdős #865, the `k = 2` case (classical folklore)

This package submits, for intake and eligibility review, a Lean proof of the classical fact recorded on the page of [JSP-000717](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000717) / [Erdős Problem #865](https://www.erdosproblems.com/865): is there `C > 0` such that every `A ⊆ {1, …, N}` with `|A| ≥ (5/8)N + C` contains distinct `a, b, c` with `a + b, a + c, b + c ∈ A`?

**Scope statement.** The Erdős–Sós question (solved by Cipollini and GPT Pro) and the general `f_k(N)` questions are not addressed. The problem page records: "It is a classical folklore fact that if `A ⊆ {1, …, 2N}` has size `≥ N + 2` then there are distinct `a, b ∈ A` such that `a + b ∈ A`, which establishes the `k = 2` case." This package proves that fact in the exact shape of the formal-conjectures statement `Erdos865.erdos_865.variants.k2` (left as `sorry` there).

## Statement and proof

[Erdos865K2/Main.lean](Erdos865K2/Main.lean) proves

```lean
theorem erdos_865_k2 (N : ℕ) :
    ∀ A ⊆ Icc 1 (2 * N), A.card ≥ N + 2 →
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∈ A
```

and its closed form `erdos_865_k2_closed`.

Proof. Let `m = min A` and `B = A ∖ {m}`, so `|B| ≥ N + 1` and `B ⊆ [m + 1, 2N]`; the translate `B − m` also lies in `[1, 2N]`, so `B` and `B − m` intersect. For `x` in the intersection, `a = m` and `b = x` are distinct elements of `A` with `a + b = m + x ∈ B ⊆ A`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
