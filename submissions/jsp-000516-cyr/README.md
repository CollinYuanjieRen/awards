# JSP-000516: the exact maximum ⌊(N+1)/2⌋ for t = 1 (Erdős #635, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000516](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000516) / [Erdős Problem #635](https://www.erdosproblems.com/635): for `t ≥ 1` and `A ⊆ {1, …, N}` such that `b − a ∤ b` whenever `a, b ∈ A` with `b − a ≥ t`, how large can `|A|` be, and is `|A| ≤ (1/2 + o_t(1)) N`? The component formalized here is the observation recorded on the problem page, **"Erdős observes that when `t = 1` the maximum possible is `|A| = ⌊(N+1)/2⌋`, achieved by taking `A` to be all odd numbers in `{1, …, N}`"**, in full: an admissible set contains no two consecutive integers, so it has at most one element in each block `{2i − 1, 2i}`, and the odd numbers are admissible. The `t = 2` construction, the general question and its resolution are **not** claimed.

## Statements

Subsets of `{1, …, N}` are Mathlib `Finset ℕ`; the admissibility predicate and the maximum are defined in this package; `⌊(N+1)/2⌋` is `(N + 1) / 2` in natural-number division (namespace `Erdos635`, [Proof/Main.lean](Proof/Main.lean)):

```lean
def Adm (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ (b - a) ∣ b

noncomputable def maxAdm (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => Adm N A)).sup Finset.card

theorem maxAdm_eq (N : ℕ) : maxAdm N = (N + 1) / 2

theorem isGreatest_adm_card (N : ℕ) :
    IsGreatest {m : ℕ | ∃ A : Finset ℕ, Adm N A ∧ A.card = m} ((N + 1) / 2)

theorem card_le_of_adm (N : ℕ) (A : Finset ℕ) (h : Adm N A) : A.card ≤ (N + 1) / 2

theorem adm_odds (N : ℕ) : Adm N ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n))

theorem card_odds (N : ℕ) : ((Finset.Icc 1 N).filter (fun n => ¬ 2 ∣ n)).card = (N + 1) / 2
```

`Adm N A` is the page's condition at `t = 1` (every pair `a < b` has `b − a ≥ 1`); `maxAdm N` is the largest size of an admissible set. The first theorem (data binder `N`) is Erdős's value; the second states it as the greatest admissible size; the third is the upper bound for every admissible set; the last two say that the odd numbers are admissible and that there are `⌊(N+1)/2⌋` of them. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `a` and `a + 1` were both in `A` then `(a + 1) − a = 1` would divide `a + 1`; so `A` has no two consecutive integers, the map `a ↦ (a + 1)/2` is injective on `A` with values in `{1, …, ⌊(N+1)/2⌋}`, and `|A| ≤ ⌊(N+1)/2⌋`. For odd `a < b` the difference `b − a` is even and cannot divide the odd number `b`, so the `⌊(N+1)/2⌋` odd numbers in `{1, …, N}` form an admissible set.

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

The problem was posed by Erdős in a letter to Ruzsa (Gu83, Ru99); the `t = 1` observation is Erdős's, as recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is Progress; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000516-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
