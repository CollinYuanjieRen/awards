# JSP-000685: a ≥2-representation certificate for sums of two cubes (scoped component)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000685](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000685): *How many representations can one integer have as a sum of two integer cubes?* (Erdős; [Ma35b] Mahler, *On the Lattice Points on Curves of Genus 1*; [St08].)

**The open question — how large this representation count can be, and whether it is unbounded — is not claimed here.** This package formalizes a fully verified **lower-bound certificate**: at least one integer admits **two** distinct representations as a sum of two positive cubes. The witness is the classical Hardy–Ramanujan taxicab number `1729`:

```
1729 = 1³ + 12³ = 1 + 1728
1729 = 9³ + 10³ = 729 + 1000
```

## Statement and proof

With `cubeReps n bound := ((Icc 1 bound) ×ˢ (Icc 1 bound)).filter (fun p => p.1 ≤ p.2 ∧ p.1^3 + p.2^3 = n)` counting the unordered positive-cube pairs summing to `n` (the `p.1 ≤ p.2` guard counts each unordered representation once), the package proves

```lean
theorem two_le_card_cubeReps_1729 : 2 ≤ (cubeReps 1729 12).card
theorem exists_two_cube_representations :
    ∃ p q : ℕ × ℕ, p ≠ q ∧ p.1 ≤ p.2 ∧ q.1 ≤ q.2 ∧
      p.1 ^ 3 + p.2 ^ 3 = 1729 ∧ q.1 ^ 3 + q.2 ^ 3 = 1729
```

Both are decided from the two explicit representations by `decide` (`native_decide` is not used). The bound `12` suffices because `12³ = 1728 ≤ 1729 < 13³`, so it contains every positive-cube representation of `1729`; therefore `2 ≤ card` is an honest lower bound on the true representation count.

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build) for mechanical statement comparison. The catalog record is in `sources/jsp-000685.md` and the numeric witness in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The certificate is elementary (a finite arithmetic check). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000685-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
