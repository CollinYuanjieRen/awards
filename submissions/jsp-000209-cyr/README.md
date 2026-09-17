# JSP-000209: a ≥6-representation certificate for integers of the form 2^k + p (scoped component of Er50)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000209](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000209): *How many representations can a single integer have as a prime plus a power of two?* (Erdős, [Er50] *On integers of the form 2^k+p and some related problems*, Summa Brasil. Math. (1950), 113–123.)

**The open question — how large this representation count can be, and whether it is unbounded — is not claimed here.** This package formalizes a clean, fully verified **lower-bound certificate**: at least one integer admits **six** distinct representations as a power of two plus a prime. The witness is the classical value `n = 105`:

| exponent k | 2^k | 105 − 2^k | prime? |
| --- | --- | --- | --- |
| 1 | 2 | 103 | ✓ |
| 2 | 4 | 101 | ✓ |
| 3 | 8 | 97 | ✓ |
| 4 | 16 | 89 | ✓ |
| 5 | 32 | 73 | ✓ |
| 6 | 64 | 41 | ✓ |

## Statement and proof

With `repExps n K := (Finset.Icc 1 K).filter (fun k => 2^k < n ∧ Nat.Prime (n - 2^k))` counting the exponents `k ∈ [1,K]` that yield a representation `n = 2^k + (n − 2^k)` with `n − 2^k` prime, the package proves

```lean
theorem card_repExps_105 : 6 ≤ (repExps 105 6).card
theorem exists_six_representations :
    ∃ S : Finset ℕ, S.card = 6 ∧ ∀ k ∈ S, Nat.Prime (105 - 2 ^ k) ∧ 2 ^ k + (105 - 2 ^ k) = 105
```

Distinct exponents give distinct representations, so counting valid exponents is an honest lower bound on the number of representations (the filter can only undercount, by ignoring `k = 0` and `k > 6`). The six memberships are decided from the primality of 103, 101, 97, 89, 73, 41 (all below 128) by `decide`/`norm_num`; the lower bound follows from `Finset.card_le_card` applied to `{1,2,3,4,5,6} ⊆ repExps 105 6`.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The catalog record is recorded verbatim in `sources/jsp-000209.md` and the numeric witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite primality check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000209-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
