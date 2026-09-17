# JSP-000850: the trivial range n < rk of the Erdős matching conjecture, f(n; r, k) = C(n, r) (Erdős #1020, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000850](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000850) / [Erdős Problem #1020](https://www.erdosproblems.com/1020): with `f(n; r, k)` the maximal number of edges of an `r`-uniform hypergraph on `n` vertices without `k` independent edges, is `f(n; r, k) = max(C(rk−1, r), C(n, r) − C(n−k+1, r))` for `r ≥ 3` (the Erdős matching conjecture)? The component formalized here is the elementary content behind the page's **"The conjecture is trivially true if `n < kr`"**, stated in the form that is actually true: for `n < rk`, `k` pairwise disjoint `r`-element edges cannot fit into `n` vertices, so every `r`-uniform hypergraph on `n` vertices is free of `k`-matchings and `f(n; r, k) = C(n, r)`. (With `f` defined on `n` vertices, the page's displayed formula fails for `n < rk − 1` and `k ≥ 2`, as the formal-conjectures project's comment on the problem records, and agrees with `C(n, r)` at `n = rk − 1`; the package proves the true value and does not assert the formula.) The conjecture for `n ≥ rk` and Frankl's bound are **not** claimed.

## Statements

A hypergraph on `n` vertices is a Mathlib `Finset (Finset (Fin n))`; the uniformity and matching predicates and `f` are defined in this package (namespace `Erdos1020`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsUniform {n : ℕ} (r : ℕ) (H : Finset (Finset (Fin n))) : Prop := ∀ e ∈ H, e.card = r

def HasMatching {n : ℕ} (k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∃ M ⊆ H, M.card = k ∧ (M : Set (Finset (Fin n))).PairwiseDisjoint id

noncomputable def f (n r k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter
    (fun H => IsUniform r H ∧ ¬ HasMatching k H)).sup Finset.card

theorem not_exists_lt_and_ne (n r k : ℕ) : ¬ (n < r * k ∧ f n r k ≠ n.choose r)

theorem f_eq_choose_of_lt (n r k : ℕ) (h : n < r * k) : f n r k = n.choose r

theorem not_hasMatching_of_lt (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (h : n < r * k) : ¬ HasMatching k H

theorem f_le_choose (n r k : ℕ) : f n r k ≤ n.choose r

theorem card_le_f (n r k : ℕ) (H : Finset (Finset (Fin n))) (hH : IsUniform r H)
    (hM : ¬ HasMatching k H) : H.card ≤ f n r k
```

`f n r k` is the page's `f(n; r, k)`, a maximum over the finitely many hypergraphs on `Fin n`. The first theorem (data binders `n`, `r`, `k`, in negation form) says that `n < rk` forces `f(n; r, k) = C(n, r)`; the second is the same in direct form; the third is the combinatorial core; the last two make `f` transparent (at most `C(n, r)`, at least the size of every admissible hypergraph). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

`k` pairwise disjoint `r`-sets in an `n`-element set have a union of exactly `rk` elements, so `rk ≤ n`; hence for `n < rk` no `r`-uniform hypergraph has `k` independent edges. The family of all `r`-subsets of the vertices is `r`-uniform and matching-free, so `f ≥ C(n, r)`; every `r`-uniform hypergraph is a subfamily of it, so `f ≤ C(n, r)`.

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

The problem is Erdős's (Er65d, Er71). The trivial range is the folklore observation recorded on the problem page. The Lean development is written from scratch in this package; the formal-conjectures statement was not consulted for the proof.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the conjecture. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000850-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
