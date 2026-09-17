# JSP-000847: the Erdős–Goodman–Pósa bound n²/4 is sharp (Erdős #1017, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000847](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000847) / [Erdős Problem #1017](https://www.erdosproblems.com/1017): let `f(n, k)` be such that every graph on `n` vertices and `k` edges can be partitioned into at most `f(n, k)` edge-disjoint complete graphs; estimate `f(n, k)` for `k > n²/4`. The component formalized here is the remark recorded on the problem page about the Erdős–Goodman–Pósa bound `f(n, k) ≤ n²/4`, **"which is best possible in general, as witnessed for example by a complete bipartite graph"**: the balanced complete bipartite graph on `n` vertices is triangle-free with `⌊n²/4⌋` edges, so every partition of its edges into complete graphs uses `⌊n²/4⌋` single edges, and `f(n, ⌊n²/4⌋) ≥ ⌊n²/4⌋`. The Erdős–Goodman–Pósa upper bound itself, its "edges and triangles" refinement, Lovász's covering theorem and the question for `k > n²/4` are **not** claimed.

## Statements

Graphs are Mathlib's `SimpleGraph`; cliques, edge sets and triangle-freeness (`CliqueFree 3`) are Mathlib's. The clique partition number, the page's `f`, and the witness graph are defined in this package (namespace `Erdos1017`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)); `edgesOf` is reused from our own JSP-000164 submission:

```lean
def edgesOf {V : Type*} [DecidableEq V] (T : Finset V) : Finset (Sym2 V) :=
  T.sym2.filter (fun e => ¬ e.IsDiag)

def IsCliquePartition {V : Type*} [DecidableEq V] (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ S ∈ P, G.IsClique (S : Set V) ∧ 2 ≤ S.card) ∧ ∀ e ∈ G.edgeSet, ∃! S, S ∈ P ∧ e ∈ edgesOf S

noncomputable def cliquePartitionNum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ P : Finset (Finset V), IsCliquePartition G P ∧ P.card = m}

noncomputable def f (n k : ℕ) : ℕ :=
  open scoped Classical in
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = k ∧ cliquePartitionNum G = m}

def balancedBipartite (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => i.val < n / 2 ∧ n / 2 ≤ j.val)

theorem sq_div_four_le_f (n : ℕ) : n ^ 2 / 4 ≤ f n (n ^ 2 / 4)

theorem cliquePartitionNum_balancedBipartite (n : ℕ) :
    cliquePartitionNum (balancedBipartite n) = n ^ 2 / 4

theorem card_edgeFinset_balancedBipartite (n : ℕ) :
    (balancedBipartite n).edgeFinset.card = n ^ 2 / 4

theorem cliquePartitionNum_eq_of_cliqueFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    cliquePartitionNum G = G.edgeFinset.card

theorem cliquePartitionNum_le_card_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : cliquePartitionNum G ≤ G.edgeFinset.card

theorem balancedBipartite_cliqueFree_three (n : ℕ) : (balancedBipartite n).CliqueFree 3
```

`IsCliquePartition G P` says the parts of `P` are complete subgraphs of `G` on at least two vertices whose edge sets partition `E(G)` (every edge lies in exactly one part; edgeless parts are excluded so that the count is honest); `cliquePartitionNum G` is the least number of parts (an `sInf` over a set the fifth theorem shows nonempty); `f n k` is the page's `f(n, k)`, the largest clique partition number of a graph on `n` vertices with `k` edges (an `sSup` over a set bounded by `k` by the fifth theorem; it is `0` when no such graph exists); `balancedBipartite n` is the complete bipartite graph on `Fin n` with parts `{i < ⌊n/2⌋}` and `{i ≥ ⌊n/2⌋}`, and `n ^ 2 / 4` is `⌊n²/4⌋ = ⌊n/2⌋·⌈n/2⌉`. The first theorem (data binder `n`) is the sharpness statement; the second and third describe the witness; the fourth is the general fact behind it (triangle-free graphs need as many cliques as they have edges); the fifth is the trivial upper bound; the sixth is triangle-freeness of the witness. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

The edges of a graph, each as a two-vertex clique, form a clique partition, so the clique partition number is at most the number of edges. In a triangle-free graph every clique has at most two vertices, so every part of a clique partition is a single edge and the map edge ↦ its part is injective; hence the clique partition number equals the number of edges. The balanced complete bipartite graph is triangle-free (two of any three vertices lie on the same side) and has `⌊n/2⌋(n − ⌊n/2⌋) = ⌊n²/4⌋` edges by the degree-sum formula; it therefore lies in the set defining `f(n, ⌊n²/4⌋)` with clique partition number `⌊n²/4⌋`, and the supremum is at least that.

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

The problem is Erdős's (Er71); the bound `f(n, k) ≤ n²/4` is Erdős–Goodman–Pósa (EGP66), and its sharpness via a complete bipartite graph is the folklore remark recorded on the problem page. The Lean development is written from scratch by us; `edgesOf` is reused from our own JSP-000164 submission, as noted in the module docstring.

This is a scoped component of a catalog record whose status is Open; it is submitted under the fleet convention "solved (scoped component)" and does not claim the Erdős–Goodman–Pósa theorem or the question for `k > n²/4`. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000847-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
