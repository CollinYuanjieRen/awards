# JSP-000520: the trivial case k = 3 of the Erdős–Hajnal odd-cycle problem — f(3) = 3 (Erdős #640, scoped component)

This package submits a Lean formalization for intake and review of a **scoped component** of [JSP-000520](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0501-0600.md#JSP-000520) / [Erdős Problem #640](https://www.erdosproblems.com/640): for `k ≥ 3`, is there `f(k)` such that every graph with chromatic number `≥ f(k)` contains an odd cycle whose vertices span a graph of chromatic number `≥ k`? The component formalized here is the case recorded on the problem page as trivial, **"This is trivial when `k = 3`, since any non-bipartite graph contains an odd cycle, and all odd cycles have chromatic number `3`"**, made precise as `f(3) = 3`: every graph with chromatic number `≥ 3` contains an odd cycle whose vertex set induces a subgraph of chromatic number `≥ 3`, and no threshold below `3` works. The existence of `f(k)` for any `k ≥ 4` (the open question) and Steiner's reformulation with paths are **not** claimed.

## Statements

Graphs, walks, cycles, induced subgraphs and chromatic numbers are Mathlib's; the threshold is defined in this package (namespace `Erdos640`, [Proof/Defs.lean](Proof/Defs.lean), [Proof/Main.lean](Proof/Main.lean)):

```lean
def SpansOddCycle (k f : ℕ) : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), (f : ℕ∞) ≤ G.chromaticNumber →
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
      (k : ℕ∞) ≤ (G.induce {x | x ∈ c.support}).chromaticNumber

noncomputable def spanThreshold (k : ℕ) : ℕ := sInf {f : ℕ | SpansOddCycle k f}

theorem spanThreshold_three : spanThreshold 3 = 3

theorem spansOddCycle_three_three : SpansOddCycle 3 3

theorem exists_oddCycle_induce_three_le {V : Type*} (G : SimpleGraph V)
    (h : 3 ≤ G.chromaticNumber) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length ∧
      3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber

theorem not_spansOddCycle_three_of_le_two (f : ℕ) (hf : f ≤ 2) : ¬ SpansOddCycle 3 f

theorem three_le_chromaticNumber_induce_of_odd {V : Type*} (G : SimpleGraph V) {v : V}
    (c : G.Walk v v) (hc : Odd c.length) :
    3 ≤ (G.induce {x | x ∈ c.support}).chromaticNumber
```

`SpansOddCycle k f` says that `f` is a valid value of the page's `f(k)` (for every graph, on any vertex type, with chromatic number `≥ f` there is an odd cycle whose vertex set spans a subgraph of chromatic number `≥ k`), and `spanThreshold k` is the least valid value. The first theorem (hypothesis-free) is `f(3) = 3`; the second and third say that `3` is valid (the third for a graph on an arbitrary vertex type); the fourth says that no `f ≤ 2` is valid; the fifth is the page's "all odd cycles have chromatic number `3`" in the form needed: the subgraph spanned by any odd closed walk has chromatic number `≥ 3`. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline

If `χ(G) ≥ 3` then `G` is not `2`-colourable, so it contains an odd cycle `c` (a closed walk of minimal odd length is a cycle). The subgraph `H` spanned by the vertices of `c` is not `2`-colourable either: a `2`-colouring of `H` colours consecutive vertices of `c` differently, and one trip around the odd closed walk returns to the start with the opposite colour. Hence `χ(H) ≥ 3`, so `3` is a valid threshold. No `f ≤ 2` is valid: the graph with two vertices and one edge has chromatic number `2 ≥ f` and no odd closed walk at all, since closed walks in a `2`-colourable graph have even length. So the least valid threshold is `3`.

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

The problem is Erdős and Hajnal's (Er97d, p. 84). The `k = 3` case is the folklore observation recorded on the problem page. [Proof/OddCycle.lean](Proof/OddCycle.lean) (non-`2`-colourable graphs contain an odd cycle) is reused from our own earlier submissions (JSP-000841, JSP-000495). The Lean development is written from scratch in this package and its predecessors.

This is a scoped component of a catalog record whose status is OPEN; it is submitted under the fleet convention "solved (scoped component)" and does not claim the page's question. The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000520-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
