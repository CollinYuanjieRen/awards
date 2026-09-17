# JSP-000188: the trivial inequality G_k(N) ≤ R_k(N) for arithmetic-progression-free subsets (Erdős #201, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000188](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000188) / [Erdős Problem #201](https://www.erdosproblems.com/201): with `G_k(N)` the largest size of a `k`-AP-free subset guaranteed in every set of `N` integers and `R_k(N)` the largest `k`-AP-free subset of `{1, …, N}`, determine `G_k(N)`, relate it to `R_k(N)`, and decide whether `R_3(N)/G_3(N) → 1`. The component formalized here is the remark recorded on the problem page, **"It is trivial that `G_k(N) ≤ R_k(N)`"** (the set `{1, …, N}` is one of the `N`-sets over which `G_k(N)` is a minimum), together with the page's values **`R_3(5) = 4`** (the set `{1, 2, 4, 5}` is 3-AP-free, and `{1, …, 5}` contains `1, 2, 3`) and **`G_3(5) ≤ 3`** (every 4-element subset of `{1, 3, 4, 5, 7}` contains a 3-term progression). The lower bound `G_3(5) ≥ 3`, the values at `N = 14`, the Komlós–Sulyok–Szemerédi bound and the limit question are **not** claimed.

## Statements

Finite sets of integers are Mathlib's `Finset ℤ`; the progression predicate and the two extremal functions are defined in this package (namespace `Erdos201`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def HasAP (k : ℕ) (S : Finset ℤ) : Prop := ∃ a d : ℤ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

def APFree (k : ℕ) (S : Finset ℤ) : Prop := ¬ HasAP k S

noncomputable def apFreeMax (k : ℕ) (T : Finset ℤ) : ℕ :=
  (T.powerset.filter (fun S => APFree k S)).sup Finset.card

noncomputable def R (k N : ℕ) : ℕ := apFreeMax k (Finset.Icc (1 : ℤ) N)

noncomputable def G (k N : ℕ) : ℕ := sInf {m : ℕ | ∃ T : Finset ℤ, T.card = N ∧ apFreeMax k T = m}

theorem G_le_R (k N : ℕ) : G k N ≤ R k N

theorem R_three_five : R 3 5 = 4

theorem G_three_five_le : G 3 5 ≤ 3

theorem apFreeMax_le_iff (k : ℕ) (T : Finset ℤ) (m : ℕ) :
    apFreeMax k T ≤ m ↔ ∀ S ⊆ T, APFree k S → S.card ≤ m

theorem G_le_apFreeMax (k N : ℕ) (T : Finset ℤ) (hT : T.card = N) : G k N ≤ apFreeMax k T
```

`apFreeMax k T` is the size of the largest `k`-AP-free subset of `T` (progressions have a positive common difference); `R k N` is the page's `R_k(N)` and `G k N` the page's `G_k(N)`, the least value of `apFreeMax k T` over all `N`-element sets `T` of integers. The first theorem (data binders `k`, `N`) is the page's inequality; the second and third are the page's values at `k = 3`, `N = 5` (the third is the upper bound only); the last two make the definitions transparent. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

`{1, …, N}` is an `N`-element set of integers, so `G_k(N) ≤ apFreeMax_k({1, …, N}) = R_k(N)`. For `R_3(5) = 4`: `{1, 2, 4, 5}` contains no 3-term progression (no two of its elements have their average in the set), while the only 5-element subset of `{1, …, 5}` is the whole set, which contains `1, 2, 3`. For `G_3(5) ≤ 3`: the five 4-element subsets of `{1, 3, 4, 5, 7}` contain `3,4,5`, `1,4,7`, `1,3,5`, `1,4,7` and `3,4,5` respectively, so every 3-AP-free subset of it has at most 3 elements.

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

The problem was first asked by Riddell (Ri69) and taken up by Erdős (Er73, Er75b, ErGr79, Er80, ErGr80). The inequality and the small values are the folklore observations recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's questions. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000188-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
