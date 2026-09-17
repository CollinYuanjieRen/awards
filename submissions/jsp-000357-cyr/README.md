# JSP-000357: Massias's density-11/32 square-sum-free construction (scoped component of Erdős #438)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000357](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000357) (Erdős Problem [#438](https://www.erdosproblems.com/438)): "How large can `A ⊆ {1, …, N}` be if `A + A` contains no square numbers?"

The problem page records that `|A| ≥ N/3` is easy (residue `1 mod 3`) and that this "can be improved to `(11/32)N` by taking all integers `≡ 1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30 (mod 32)`, as observed by Massias." **This package formalizes exactly that lower-bound construction.** The matching upper bounds — Lagarias–Odlyzko–Shearer's sharp `11/32` for the modular problem and Khalfalah–Lodha–Szemerédi's `(11/32 + o(1))N` for the integer problem — are the harder results and are **not** claimed here.

## Statement and proof

`Jsp357/Massias.lean` defines, with `R = {1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30}` the eleven residues,

```lean
def A (N : ℕ) : Finset ℕ := (Finset.Icc 1 N).filter (fun x => x % 32 ∈ R)
```

and proves

```lean
theorem sq_mod_32 {m : ℕ} (h : IsSquare m) : m % 32 ∈ ({0, 1, 4, 9, 16, 17, 25} : Finset ℕ)
theorem A_sum_not_square {N a b : ℕ} (ha : a ∈ A N) (hb : b ∈ A N) : ¬ IsSquare (a + b)
theorem A_card_block (q : ℕ) : (A (32 * q)).card = 11 * q
theorem A_card_ge (N : ℕ) : 11 * (N / 32) ≤ (A N).card
theorem massias_square_sum_free (q : ℕ) :
    (∀ a ∈ A (32 * q), ∀ b ∈ A (32 * q), ¬ IsSquare (a + b)) ∧ (A (32 * q)).card = 11 * q
```

The square-sum-free property is the residue fact that every perfect square is `≡ 0, 1, 4, 9, 16, 17, 25 (mod 32)` (`sq_mod_32`), while for all `r, s ∈ R` the sum `r + s` avoids those residues mod 32; hence no two elements of `A` sum to a square. The count `A_card_block` is exact: each block of 32 consecutive integers contributes exactly the 11 residues in `R`, so `|A(32q)| = 11q`, giving density exactly `11/32` along `N = 32q`; `A_card_ge` is the resulting `11⌊N/32⌋` bound for every `N`. All checks are kernel-verified; nothing beyond the construction and its density is asserted.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and `massias_square_sum_free` with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/438, retrieved 2026-09-16) is recorded verbatim in `sources/erdos438-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of the theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp357/`, `Jsp357.lean`, `Audit.lean`); the only `sorry` in the package is the single statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The construction is Massias's (reported by Erdős [Er80c]; the sharpness results are LOS83 and KLS02). **Prior art:** an independent Lean 4 formalization of Erdős #438 exists in the public third-party repository plby/lean-proofs (`ErdosProblems/Erdos438.lean`); this package was authored independently, without reading or copying that source, and formalizes the lower-bound construction on its own definitions. The contribution sought is this independent formalization, following the fleet convention for scoped components. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000357-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
