# JSP-000385: finite prime-sum permutations for 2 ≤ n ≤ 10 (scoped component of Erdős #473)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000385](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000385) (Erdős Problem [#473](https://www.erdosproblems.com/473), Segal): is there a permutation of the positive integers such that every adjacent sum is prime?

The infinite version was solved (yes, Odlyzko). Segal's **finite version** asks, for all `n ≥ 2`, for a permutation of `{1,…,n}` with all adjacent sums prime. **The infinite version and the general finite version are not claimed here.** This package formalizes explicit certificates verifying the finite version for every `2 ≤ n ≤ 10`.

## Statement and proof

With `HasPrimeSumPerm n := ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ l.Chain' (fun a b => Nat.Prime (a + b))` (a permutation of `[1,…,n]` whose consecutive sums are all prime), the package proves `hasPrimeSumPerm_two, …, hasPrimeSumPerm_ten` and

```lean
theorem hasPrimeSumPerm_of_le_ten {n : ℕ} (h2 : 2 ≤ n) (h10 : n ≤ 10) : HasPrimeSumPerm n
```

Each `n` is witnessed by an explicit permutation (e.g. `n = 10`: `[1,2,3,4,7,6,5,8,9,10]`, with adjacent sums `3,5,7,11,13,11,13,17,19` all prime), and the combined theorem case-splits on `n`. All checks are kernel-verified (`decide`).

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/473, retrieved 2026-09-17) is recorded verbatim in `sources/erdos473-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The finite certificates are elementary checks. **Prior art:** an independent Lean formalization of #473 exists in plby/lean-proofs; this package was authored independently, without reading or copying that source. Prepared with Claude (Anthropic) assistance and locally checked. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000385-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
