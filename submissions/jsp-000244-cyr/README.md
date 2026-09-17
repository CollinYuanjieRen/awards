# JSP-000244: the sharpness example 1 = 1/2 + 1/3 + 1/6 (Erdős #287, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000244](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000244) / [Erdős Problem #287](https://www.erdosproblems.com/287): for `k ≥ 2` and distinct integers `1 < n₁ < ⋯ < n_k` with `1 = 1/n₁ + ⋯ + 1/n_k`, must `max (n_{i+1} − n_i) ≥ 3`? The component formalized here is the remark recorded on the problem page, **"The example `1 = 1/2 + 1/3 + 1/6` shows that `3` would be best possible here"**: the representation `[2, 3, 6]` has consecutive gaps `1` and `3`, so its maximal gap is exactly `3` and the constant `3` in the question cannot be replaced by `4`. The conjecture itself, the `≥ 2` half (Erdős 1932) and the conditional statement about primes `p` with `(p+1)/2` prime are **not** claimed.

## Statements

A representation is a list of natural numbers; the two definitions are this package's (namespace `Erdos287`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def UnitFractionRep (l : List ℕ) : Prop :=
  l.IsChain (· < ·) ∧ 1 < l.headI ∧ (l.map (fun n => (n : ℚ)⁻¹)).sum = 1

def maxGap (l : List ℕ) : ℕ :=
  ((l.zip l.tail).map (fun p => p.2 - p.1)).foldr max 0

theorem not_forall_four_le_maxGap :
    ¬ ∀ l : List ℕ, UnitFractionRep l → 2 ≤ l.length → 4 ≤ maxGap l

theorem unitFractionRep_example : UnitFractionRep [2, 3, 6]

theorem maxGap_example : maxGap [2, 3, 6] = 3

theorem exists_unitFractionRep_maxGap_eq_three :
    ∃ l : List ℕ, UnitFractionRep l ∧ 2 ≤ l.length ∧ maxGap l = 3
```

`UnitFractionRep l` says that `l = [n₁, …, n_k]` is strictly increasing with `1 < n₁` (so the entries are distinct and nonzero and the rational reciprocals are genuine) and `Σ 1/nᵢ = 1`; `maxGap l` is `max (n_{i+1} − n_i)` over the consecutive pairs (`0` when `k ≤ 1`). The first theorem (a closed statement, no binders) is the sharpness claim: the question's inequality with `3` replaced by `4` is false; the other three exhibit the page's example. There are no hypotheses, no custom axioms and no unproved inputs.

## Proof outline

`2 < 3 < 6`, `1 < 2` and `1/2 + 1/3 + 1/6 = 1` in `ℚ`; the consecutive gaps of `[2, 3, 6]` are `1` and `3`, so the maximal gap is `3`, and `4 ≤ 3` is false.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorem (and a subset of these for the others; `maxGap_example` is axiom-free). These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős and Graham's (ErGr80). The example `1 = 1/2 + 1/3 + 1/6` is the classical one recorded on the problem page. The Lean development is written from scratch in this package. The formal-conjectures repository independently contains a proof of the same example (its `erdos_287.test.best_possible`); nothing from it is imported or copied here.

This is a scoped component of a catalog record whose status is Open; it is submitted under the fleet convention "solved (scoped component)" and does not claim the conjecture. The contribution sought is formalization, not a new mathematical result; the mathematical content is a one-line example. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000244-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
