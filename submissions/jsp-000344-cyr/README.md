# JSP-000344: the trivial inequality V'(x) ≤ V(x) for counts of totient values (Erdős #417, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000344](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0301-0400.md#JSP-000344) / [Erdős Problem #417](https://www.erdosproblems.com/417): with `V'(x) = #{φ(m) : 1 ≤ m ≤ x}` and `V(x) = #{φ(m) ≤ x : 1 ≤ m}`, does `lim V(x)/V'(x)` exist, and is it `> 1`? The component formalized here is the remark recorded on the problem page, **"It is trivial that `V'(x) ≤ V(x)`"**: every value `φ(m)` with `m ≤ x` is a totient value `≤ x` because `φ(m) ≤ m`. The existence of the limit, whether it exceeds `1`, and Erdős's suggestion that it is infinite are **not** claimed.

## Statements

`Nat.totient` is Mathlib's Euler φ; the two value sets and the two counting functions are defined in this package (namespace `Erdos417`, [Proof/Main.lean](Proof/Main.lean)):

```lean
def totientValues (x : ℕ) : Finset ℕ := (Finset.Icc 1 x).image Nat.totient

noncomputable def totientValuesLE (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter (fun v => ∃ m, 1 ≤ m ∧ Nat.totient m = v)

def V' (x : ℕ) : ℕ := (totientValues x).card

noncomputable def V (x : ℕ) : ℕ := (totientValuesLE x).card

theorem V'_le_V (x : ℕ) : V' x ≤ V x

theorem totientValues_subset (x : ℕ) : totientValues x ⊆ totientValuesLE x

theorem mem_totientValues (x v : ℕ) :
    v ∈ totientValues x ↔ ∃ m, 1 ≤ m ∧ m ≤ x ∧ Nat.totient m = v

theorem mem_totientValuesLE (x v : ℕ) :
    v ∈ totientValuesLE x ↔ v ≤ x ∧ ∃ m, 1 ≤ m ∧ Nat.totient m = v

theorem V'_le_V_real (x : ℝ) : V' ⌊x⌋₊ ≤ V ⌊x⌋₊
```

`V' x` is the page's `V'(x)` and `V x` the page's `V(x)` (the number of distinct totient values `≤ x`). The first theorem (single data binder `x`) is the page's inequality; the second is the inclusion behind it; the third and fourth unfold the two sets to their membership conditions; the fifth restates the inequality for a real argument through `⌊x⌋`. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `v = φ(m)` with `1 ≤ m ≤ x` then `v ≤ m ≤ x` (Mathlib's `Nat.totient_le`) and `v` is a totient value, so `v` lies in the second set; hence the first set is contained in the second and `V'(x) ≤ V(x)`.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for the root theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The problem is Erdős's (Er79e, ErGr80, Er98). The inequality is the folklore observation recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000344-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
