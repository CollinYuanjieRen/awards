# JSP-000966: the (n−1)! lower bound on the maximal order-count in Sₙ (scoped component of Erdős #1161)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000966](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0901-1000.md#JSP-000966) (Erdős Problem [#1161](https://www.erdosproblems.com/1161)): let `f_k(n)` count the elements of the symmetric group `S_n` of order `k`; for which `k` is `f_k(n)` maximal?

**Beker's full answer — `max_k f_k(n) ∼ (n−1)!` together with the exact `lcm{1,…,n−k} ∣ k` characterization — is hard and is not claimed here.** This package formalizes the clean elementary **lower bound**: the maximum is at least `(n−1)!`, because the `n`-cycles all have order `n` and number exactly `(n−1)!`.

## Statement and proof

With `f n k := #{ g : Perm (Fin n) | orderOf g = k }`, the package proves

```lean
theorem factorial_le_f (n : ℕ) (hn : 2 ≤ n) : (n - 1)! ≤ f n n
theorem factorial_le_max (n : ℕ) (hn : 2 ≤ n) : ∃ k, (n - 1)! ≤ f n k
```

An `n`-cycle has cycle type `{n}`, hence order equal to `lcm{n} = n`, so the `(n−1)!` `n`-cycles all lie in `{g | orderOf g = n}`; therefore `(n−1)! ≤ f n n`, and the maximum over `k` is at least `(n−1)!`. The count of `n`-cycles is Mathlib's `Equiv.Perm.card_of_cycleType_singleton` (with `\binom{n}{n} = 1`), and `orderOf = cycleType.lcm` is `Equiv.Perm.lcm_cycleType`.

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/1161, retrieved 2026-09-17) is recorded verbatim in `sources/erdos1161-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The lower bound (the `n`-cycles) is elementary. **Prior art:** an independent Lean formalization of #1161 exists in plby/lean-proofs; this package was authored independently, without reading or copying that source. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000966-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
