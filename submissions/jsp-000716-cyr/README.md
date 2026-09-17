# JSP-000716: a size-5 subset of {1,…,8} with a single multiply-represented sum (scoped certificate, both conventions)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000716](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md#JSP-000716): how large a subset of `{1,…,N}` can be if at most one of its pairwise sums has more than one representation (a near-Sidon problem).

**The open question — the asymptotic maximum size — is not claimed here.** This package formalizes one explicit certificate: `A = {1, 2, 4, 6, 7} ⊆ {1,…,8}` has size 5 and exactly one sum value with more than one representation, namely `8 = 1 + 7 = 2 + 6` (`= 4 + 4` as well when doubles are counted). The certificate is proved under **both** conventions: pairs `x < y` (doubles excluded) and the standard Sidon/`B₂` convention `x ≤ y` (doubles included). Under the standard convention the largest Sidon subset of `{1,…,8}` has size 4, and `A` is one of the two size-5 subsets with a single repeated sum.

## Statement and proof

```lean
def A : Finset ℕ := {1, 2, 4, 6, 7}
def pairs (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 < p.2)
def multiRepSums (A : Finset ℕ) : Finset ℕ :=
  ((pairs A).image (fun p => p.1 + p.2)).filter
    (fun s => 2 ≤ ((pairs A).filter (fun p => p.1 + p.2 = s)).card)
def pairsLoose (A : Finset ℕ) : Finset (ℕ × ℕ) := (A ×ˢ A).filter (fun p => p.1 ≤ p.2)
def multiRepSumsLoose (A : Finset ℕ) : Finset ℕ := … (same with pairsLoose)

theorem A_card : A.card = 5
theorem A_subset : A ⊆ Finset.Icc 1 8
theorem A_multiRepSums : multiRepSums A = {8}
theorem A_at_most_one_repeat : (multiRepSums A).card ≤ 1
theorem A_multiRepSumsLoose : multiRepSumsLoose A = {8}
theorem A_at_most_one_repeat_loose : (multiRepSumsLoose A).card ≤ 1
```

All facts are closed by kernel `decide` over the ten (resp. fifteen) pairs (standard `Finset` decidability instances; no `native_decide`).

`Challenge.lean` is a comparator-style module (the same Mathlib-only definitions and statements with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000716.md` and the witness note in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the six theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry` is the statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is a finite computation. No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed (its one wording correction is incorporated). No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000716-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
