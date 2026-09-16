# JSP-000660: balanced subgraphs of dense graphs — Alon's construction (Erdős #803)

This package submits a Lean formalization for intake and review of [JSP-000660](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0601-0700.md#JSP-000660) / [Erdős Problem #803](https://www.erdosproblems.com/803): must every graph on `n` vertices with at least `n log n` edges (for `n` large in terms of `m`) contain a `O(1)`-balanced subgraph on `m` vertices with `≫ m log m` edges? (A graph is `D`-balanced when its maximum degree is at most `D` times its minimum degree.) The answer is no, by a construction of Noga Alon (2008); this package formalizes that construction and derives the negative answer.

## Statements

All definitions are our own (namespace `Erdos803`, [Proof/Defs.lean](Proof/Defs.lean)). For a subgraph `H : G.Subgraph` of a Mathlib simple graph, `sdeg H v` is the number of `H`-neighbours of `v`, and

```lean
def Balanced (D : ℝ) (H : G.Subgraph) : Prop :=
  ∀ v ∈ H.verts, ∀ w ∈ H.verts, (sdeg H v : ℝ) ≤ D * sdeg H w
```

The Erdős–Simonovits question with constants `ε`, `D` is recorded in two readings: `ErdosSimonovitsUniform ε D` (for every `m₀`, all large graphs with `n log₂ n` edges contain a `D`-balanced subgraph on at least `m₀` vertices with at least `ε m log₂ m` edges) and `ErdosSimonovitsLiteral ε D` (exactly `m` vertices). [Proof/Main.lean](Proof/Main.lean) proves:

```lean
theorem alon_construction (D : ℝ) (hD : 1 ≤ D) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ G : SimpleGraph (Fin N),
      (N : ℝ) * Real.logb 2 N ≤ G.edgeSet.ncard ∧
        ∀ H : G.Subgraph, Balanced D H →
          (H.edgeSet.ncard : ℝ) ≤ 18 * H.verts.ncard *
            (4 * Real.sqrt (Real.logb 2 H.verts.ncard) + Real.logb 2 (64 * D) + 26)

theorem not_erdosSimonovitsUniform : ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsUniform ε D

theorem not_erdosSimonovitsLiteral : ¬ ∃ ε D : ℝ, 0 < ε ∧ 0 < D ∧ ErdosSimonovitsLiteral ε D
```

The first theorem is Alon's Proposition 2.1 (his bound is on the average degree, `36(4√log₂ m + log₂(64D) + 18)`; our integer threshold parameter costs the additive constant 26 instead of 18 and does not affect the conclusion). The other two theorems are the negative answer to the question in both readings; the literal reading implies the uniform one. There are no hypotheses beyond those displayed, no custom axioms and no unproved inputs.

## Proof outline (Alon 2008, Section 2)

Let `A = Fin n`; for `4 ≤ i ≤ ⌊log₂ n⌋/2` and `j < 8`, block `(i, j)` has `⌊n / 2ⁱ⌋` vertices, so all blocks together have at most `n` vertices ([Proof/Model.lean](Proof/Model.lean)). A choice function gives every `a ∈ A` one neighbour in every block; the resulting bipartite graph has `8·#i` edges at every `a`, hence at least `N log₂ N` edges after padding to `N` vertices. A choice function is *good* if for all `m ≤ n`, every `A' ⊆ A` with `|A'| ≤ m` and every set `B'` of at most `m` vertices in blocks of size at least `m·2^{r(m)}`, fewer than `m·r(m)` edges join `A'` to `B'`, where `r(m) = 4(⌊√⌊log₂ m⌋⌋+1) + 16`. A prescribed set of pairs is realised by at most `|Choice| / ∏ (block sizes)` choice functions, and a union bound ([Proof/Counting.lean](Proof/Counting.lean)) with the estimates of [Proof/Estimates.lean](Proof/Estimates.lean) shows that fewer than `|Choice|` choice functions are bad for `n ≥ 2⁴⁰`, so a good one exists ([Proof/Existence.lean](Proof/Existence.lean)). For a good choice function and a `D`-balanced subgraph `H` with `m` vertices and minimum degree `d`, the edges of `H` are split by the size of their block endpoint: small blocks (size `≤ m/(64D)`) carry at most `m d/4` edges, at most `8(r + log₂(64D) + 2)` middle blocks each carry at most `m` edges, and large blocks carry fewer than `m r` edges by goodness; with `2e(H) ≥ m d` this gives `e(H) ≤ 18 m (r + log₂(64D) + 2)` ([Proof/Deterministic.lean](Proof/Deterministic.lean)). [Proof/Transfer.lean](Proof/Transfer.lean) moves the graph to `Fin N` with isolated padding vertices (a balanced subgraph containing an isolated vertex has no edges).

## Reproduce

Install Lean through elan, then run in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) re-checks the three root statements with typed `example`s, prints the definitions and prints the axioms of the roots. [verification.txt](verification.txt) records the local build and audit of this exported package. [Challenge.lean](Challenge.lean) is a comparator-style module (Mathlib-only definitions and the three statements with `sorry`).

## Axiom audit

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for all three theorems. These are the standard foundational axioms of Lean's core library on which Mathlib is built (propositional extensionality, the axiom of choice, quotient soundness). The development introduces no project axiom, no `sorry`/`admit`, no `native_decide` or other trusted-code shortcut, and no hypothesis beyond those of the stated theorems. The official rules (Section 6, offline verification with axiom audits; Section 7, revocation for placeholder or unreviewed axioms) do not enumerate accepted axioms; the three listed here are disclosed for that audit, and no operator ruling on their acceptability is claimed.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations, and no claim is made that this release candidate meets an operator-designated minimum safe version. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and scope

The question is due to P. Erdős and M. Simonovits (Some extremal problems in graph theory, 1970); the construction and the negative answer are due to Noga Alon, *Problems and results in extremal combinatorics II*, Discrete Mathematics 308 (2008), 4460–4472, Section 2, Proposition 2.1 ([DOI](https://doi.org/10.1016/j.disc.2007.08.090)). The complementary positive result of Janzer and Sudakov (2023) is not part of the question as recorded and is not formalized. The statements formalized here are the `n log n` / `m log m` question exactly as recorded on the problem page and in Alon's Section 2, together with Alon's construction; the polynomial-density variant with `n^{1+α}` edges (Erdős Problem #1077), which is refuted by a complete bipartite graph, is a different and much weaker statement and is not what this package formalizes. The Lean development is written from scratch in this package.

The contribution sought is formalization, not a new mathematical result. The Lean code was prepared with Claude Code (Anthropic) assistance and checked locally. This is a self-submission with a direct interest in the review outcome.

Proposed formalizer: `RECIPIENT-jsp-000660-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. Please redirect if another location is required.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
