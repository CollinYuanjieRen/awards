# JSP-000164: the trivial bound τ(G) ≤ 3ν(G) for triangle packings and covers (Erdős #167, Tuza's conjecture, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000164](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0101-0200.md#JSP-000164) / [Erdős Problem #167](https://www.erdosproblems.com/167) (Tuza's conjecture): if `G` has at most `k` edge-disjoint triangles, can `G` be made triangle-free by removing at most `2k` edges? The component formalized here is the bound recorded on the problem page as trivial, **"It is trivial that `G` can be made triangle-free after removing at most `3k` edges"**: deleting the edges of a maximal family of pairwise edge-disjoint triangles (at most `3k` edges) leaves no triangle, since a surviving triangle could be added to the family. In packing/covering language, the triangle cover number `τ(G)` is at most `3ν(G)`. Tuza's `2k` conjecture, the `K₄`/`K₅` sharpness examples, Haxell's improvement and the Kahn–Park random-graph result are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph` on a finite vertex type; triangles are 3-element cliques, packings are families of pairwise edge-disjoint triangles, covers are edge sets whose deletion leaves the graph triangle-free; the packing and cover numbers are defined in this package (namespace `Erdos167`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
noncomputable def triangles {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Finset V) :=
  ((Finset.univ : Finset V).powersetCard 3).filter (fun T => G.IsClique (T : Set V))

def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ¬ e.IsDiag)

def IsPacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Finset V)) : Prop :=
  F ⊆ triangles G ∧ (F : Set (Finset V)).PairwiseDisjoint edgesOf

noncomputable def packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset (Finset V))).filter (fun F => IsPacking G F)).sup Finset.card

def IsCover {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3

noncomputable def coverNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = m}

theorem not_exists_coverNumber_gt (n : ℕ) :
    ¬ ∃ G : SimpleGraph (Fin n), 3 * packingNumber G < coverNumber G

theorem coverNumber_le_three_mul_packingNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : coverNumber G ≤ 3 * packingNumber G

theorem exists_cover_of_packingNumber_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (hk : packingNumber G ≤ k) :
    ∃ D : Finset (Sym2 V), D.card ≤ 3 * k ∧ (G.deleteEdges (D : Set (Sym2 V))).CliqueFree 3

theorem coverNumber_le_card {V : Type*} (G : SimpleGraph V) (D : Finset (Sym2 V)) (h : IsCover G D) :
    coverNumber G ≤ D.card

theorem exists_isCover_card_eq {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ D : Finset (Sym2 V), IsCover G D ∧ D.card = coverNumber G

theorem card_le_packingNumber {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Finset V)) (h : IsPacking G F) : F.card ≤ packingNumber G
```

`packingNumber G` is `ν(G)` ("`G` has at most `k` edge-disjoint triangles" is `ν(G) ≤ k`) and `coverNumber G` is `τ(G)`. The first theorem (data binder `n`, in negation form) says `τ(G) ≤ 3ν(G)` for every graph on `n` vertices; the second is the same for any finite vertex type; the third is the page's sentence in its `k`-form; the last three make `τ` and `ν` transparent (`τ` is a lower bound of the covers and is attained; `ν` is an upper bound of the packings). There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

Let `F` be a packing of maximum size and `D` the union of the edge sets of its members, so `|D| ≤ 3|F| ≤ 3ν(G)`. If a triangle `T` survived in `G − D`, its three edges would lie outside `D`, so `T` would be edge-disjoint from every member of `F` and not in `F`; then `F ∪ {T}` would be a larger packing. Hence `D` is a cover and `τ(G) ≤ 3ν(G)`; for the `k`-form, `D` has at most `3k` edges.

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

The problem is Tuza's, recorded by Erdős (Er88). The `3k` bound is the folklore observation recorded on the problem page. The Lean development is written from scratch in this package.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim Tuza's conjecture. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000164-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
