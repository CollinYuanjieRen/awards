# JSP-000430: a chain with no three equal pairwise LCMs, and a realizable forbidden triple (scoped certificates)

This package submits a Lean formalization for intake and eligibility review of a **scoped component** of [JSP-000430](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000430): *How large can an integer set be if no three elements have equal pairwise least common multiples?*

**The open (recently studied) question — the maximum size of such a set, of order `N` — is not claimed here.** This package formalizes two elementary facts:

1. **Construction.** The divisibility chain `{1, 2, 4, 8, 16, 32}` has no three elements with all three pairwise LCMs equal.
2. **Realizability of the forbidden configuration.** `lcm(6,10) = lcm(6,15) = lcm(10,15) = 30`.

## Statement and proof

```lean
def C : Finset ℕ := {1, 2, 4, 8, 16, 32}

theorem C_no_equal_lcm_triple :
    ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a < b → b < c →
      ¬ (Nat.lcm a b = Nat.lcm a c ∧ Nat.lcm a c = Nat.lcm b c)
theorem bad_triple : Nat.lcm 6 10 = 30 ∧ Nat.lcm 6 15 = 30 ∧ Nat.lcm 10 15 = 30
```

Both are decided over `Nat.lcm` by `decide`. The `a < b < c` guard covers each unordered triple once (pairwise-LCM equality is symmetric).

`Challenge.lean` is a comparator-style module (the same Mathlib-only definition and two targets with `sorry`, not imported by the build). The catalog record is in `sources/jsp-000430.md` and the witnesses in `sources/witness.txt`, with SHA-256 digests in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. `Audit.lean` prints the axioms of the two theorems: a subset of `[propext, Classical.choice, Quot.sound]`. No `sorry`, custom axioms, `native_decide`, or `opaque`/`unsafe`/`implemented_by`/`partial` in the built library; the only `sorry`s are the statement-only targets of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

Both facts are elementary (finite `lcm` checks). No third-party Lean formalization of this record is known to the author; this package was authored independently. Prepared with Claude (Anthropic) assistance (design by Claude Fable 5.1, Lean implementation by a Claude Opus subagent) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000430-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
