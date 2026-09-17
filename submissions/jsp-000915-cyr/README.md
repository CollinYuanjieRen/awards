# JSP-000915: a set with all pairwise sums squarefree (scoped certificate)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000915](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000915): *Is there an infinite sequence with every pairwise sum squarefree, and how slowly can it grow?*

**The open question — the existence of such an infinite sequence and its growth rate — is not claimed here.** This package formalizes a fully verified **certificate**: the finite set `S = {1, 2, 4, 9, 13}` has all of its distinct pairwise sums squarefree. The ten sums are

```
3, 5, 6, 10, 11, 13, 14, 15, 17, 22,
```

each squarefree.

## Statement and proof

```lean
def S : Finset ℕ := {1, 2, 4, 9, 13}

theorem S_pairwise_sum_squarefree :
    ∀ a ∈ S, ∀ b ∈ S, a < b → Squarefree (a + b)
theorem exists_squarefree_sum_set :
    ∃ T : Finset ℕ, T.card = 5 ∧ ∀ a ∈ T, ∀ b ∈ T, a < b → Squarefree (a + b)
```

`Squarefree` is Mathlib's squarefree predicate. Each of the ten sums is shown squarefree by hand: the primes via `Nat.Prime.squarefree`, and the semiprimes via `Nat.squarefree_mul` of coprime primes (`Nat.coprime_primes`). The pairs are enumerated by `fin_cases`. The statement uses the distinct-pair reading `a < b`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000915.md` and the witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite squarefree check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000915-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
