# JSP-000150: τ(G) ≤ n − H(n) for triangle-free graphs (Erdős #151, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000150](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000150) / [Erdős Problem #151](https://www.erdosproblems.com/151): for a graph `G` let `τ(G)` be the least number of vertices meeting every maximal clique of `G` on at least two vertices (the clique transversal number), and let `H(n)` be the largest `h` such that every triangle-free graph on `n` vertices contains an independent set on `h` vertices; is `τ(G) ≤ n − H(n)` for every graph `G` on `n` vertices? The component formalized here is the remark recorded on the problem page, **"if `G` is triangle-free then trivially `τ(G) ≤ n − H(n)`"**: the complement of a maximum independent set meets every clique on two or more vertices, so `τ(G) ≤ n − α(G)`, and `H(n) ≤ α(G)` when `G` is triangle-free. The general question for arbitrary `G`, the bound `τ(G) ≤ n − √n` and the `K₄`-free case are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph`; maximal cliques are Mathlib's `Maximal G.IsClique`; independent sets and the independence number `α(G)` are Mathlib's `SimpleGraph.IsIndepSet` and `SimpleGraph.indepNum`. The clique transversal number and `H` are defined in this package (namespace `Erdos151`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def IsCliqueTransversal {V : Type*} (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∀ s : Finset V, Maximal G.IsClique (s : Set V) → 2 ≤ s.card → ∃ v ∈ T, v ∈ s

noncomputable def cliqueTransversalNum {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ T : Finset V, T.card = k ∧ IsCliqueTransversal G T}

noncomputable def H (n : ℕ) : ℕ :=
  sSup {h : ℕ | ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → h ≤ G.indepNum}

theorem not_exists_triangleFree_gt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ n - H n < cliqueTransversalNum G

theorem cliqueTransversalNum_le_of_cliqueFree (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNum G ≤ n - H n

theorem cliqueTransversalNum_le_card_sub_indepNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : cliqueTransversalNum G ≤ Fintype.card V - G.indepNum

theorem H_le_indepNum (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.CliqueFree 3) :
    H n ≤ G.indepNum

theorem isCliqueTransversal_compl_of_isIndepSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    IsCliqueTransversal G (Finset.univ \ S)
```

`cliqueTransversalNum G` is `τ(G)` (an `sInf` over a nonempty set, since the whole vertex set is a transversal) and `H n` is the page's `H(n)` (an `sSup` over a set that contains `0` and is bounded by the independence number of the edgeless graph; the fourth theorem says it is attained). The first theorem (data binder `n`, in negation form) says `τ(G) ≤ n − H(n)` for every triangle-free graph on `n` vertices; the second is the same in direct form; the third is the general bound `τ(G) ≤ |V| − α(G)` for every graph on a finite vertex type; the last is the one-line combinatorial core. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `S` be an independent set. A clique `s` on at least two vertices contains two distinct vertices, which are adjacent, so they are not both in `S`; hence `V ∖ S` meets `s`. Taking `S` of size `α(G)` gives a transversal of size `|V| − α(G)`, so `τ(G) ≤ |V| − α(G)`. The set defining `H(n)` contains `0` and is bounded above by `α` of the edgeless graph (which is triangle-free), so its supremum belongs to it, i.e. `H(n) ≤ α(G)` for every triangle-free `G` on `n` vertices. Combining, `τ(G) ≤ n − α(G) ≤ n − H(n)`.

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

The problem is due to Erdős and Gallai (Er88; EGT92). The triangle-free remark is the folklore observation recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the general question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000150-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
