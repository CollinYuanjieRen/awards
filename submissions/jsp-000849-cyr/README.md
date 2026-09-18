# JSP-000849: saturated planar subgraphs at ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges (Erdős #1019)

This package submits a Lean formalization for intake and eligibility review. It answers [JSP-000849](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000849), which is [Erdős Problem #1019](https://www.erdosproblems.com/1019): a planar graph on m vertices with 3m − 6 edges is called saturated; does every graph on n vertices with ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges contain a saturated planar graph with more than three vertices? The answer is yes (Simonovits).

## Statement and proof

[Erdos1019Planar/Main.lean](Erdos1019Planar/Main.lean) proves `erdos_1019_saturated_planar`:

```lean
theorem erdos_1019_saturated_planar {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V)
    (hE : G.edgeSet.ncard = Fintype.card V * Fintype.card V / 4 + (Fintype.card V + 1) / 2) :
    ∃ (W : Type) (_ : Fintype W) (H : SimpleGraph W),
      H.IsPlanar ∧ 3 < Fintype.card W ∧ H.edgeSet.ncard = 3 * Fintype.card W - 6 ∧ H ⊑ G
```

Here `G` is a finite simple graph on `n = Fintype.card V ≥ 1` vertices, `G.edgeSet.ncard` is its number of edges, and `/` is natural-number floor division, so the hypothesis is exactly `⌊n²/4⌋ + ⌊(n+1)/2⌋` edges. The conclusion exhibits a finite graph `H` on more than three vertices that is planar, has exactly `3 · |W| − 6` edges, and is contained in `G` (`H ⊑ G` is Mathlib's `SimpleGraph.IsContained`: an injective graph homomorphism from `H` to `G`). The nonemptiness assumption only excludes the empty graph, for which the literal statement is false and which the problem does not intend.

Planarity is the ordinary topological notion, defined in [Erdos1019Planar/Planarity.lean](Erdos1019Planar/Planarity.lean): `SimpleGraph.IsPlanar H` means there is a plane drawing of `H` in `ℝ × ℝ`, that is, distinct vertex positions and, for every edge, a Jordan arc (the injective continuous image of `[0, 1]`) joining the positions of its endpoints, such that no vertex lies on the arc of a non-incident edge and two distinct arcs meet only in positions of common endpoints. No combinatorial certificate, Euler-formula bookkeeping, or "planar means isomorphic to a known planar graph" shortcut is used.

The proof has two parts.

1. **Simonovits's theorem** ([Erdos1019Planar/Simonovits.lean](Erdos1019Planar/Simonovits.lean), `Erdos1019.erdos_1019_sharp`): a graph with the stated number of edges contains `K₄` or a bipyramid `C_l + 2K₁` with `l ≥ 3`. This Lean proof is the file [plby/lean-proofs `src/latest/ErdosProblems/Erdos1019.lean` at commit 8822f7dd](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1019.lean) (formal authors Codex and GPT-5.6 Sol, informal author Miklós Simonovits). It is **not redistributed** by this package: `fetch_sources.py` downloads it from that pinned public location, verifies its SHA-256 (`476e3920…`), applies the two recorded edits (the removal of a trailing `#print axioms` and one deprecation fix marked `-- PORT:`) and verifies the adapted SHA-256 (`fce15603…`) recorded in [external-proof-sources.json](external-proof-sources.json); the generated file `Erdos1019Planar/Simonovits.lean` is gitignored. That file's own final theorem states planarity only as "isomorphic to `K₄` or to a bipyramid" (`CanonicalPlanarTriangulationModel`); this package does not use that predicate.
2. **Planarity bridge** (new): `SimpleGraph.IsPlanar.of_isStraightLineDrawing` ([StraightLine.lean](Erdos1019Planar/StraightLine.lean)) shows that a crossing-free straight-line placement is a plane drawing, with the affine parametrization of each segment as the Jordan arc. [K4.lean](Erdos1019Planar/K4.lean) draws `K₄` at `(0,0), (4,0), (0,4), (1,1)`. [BipyramidLines.lean](Erdos1019Planar/BipyramidLines.lean), [BipyramidChords.lean](Erdos1019Planar/BipyramidChords.lean), [BipyramidSpokes.lean](Erdos1019Planar/BipyramidSpokes.lean) and [Bipyramid.lean](Erdos1019Planar/Bipyramid.lean) draw the bipyramid over the `l`-cycle with the equator at `(i, i²)` on the parabola `y = x²`, the inner apex at `(1, 3/2)` and the outer apex at `(0, −l²)`; every non-crossing claim is reduced to the sign of an explicit affine functional ([Separation.lean](Erdos1019Planar/Separation.lean)). `K₄` has `6 = 3·4 − 6` edges and the bipyramid has `3l = 3(l+2) − 6` edges, which gives the saturated edge count.

The same file also states the result as a single closed proposition, `erdos_1019_saturated_planar_closed`: there is no graph on `n + 1 ≥ 1` vertices (on the vertex type `Fin (n + 1)`, which covers every finite graph up to isomorphism) with `⌊(n+1)²/4⌋ + ⌊(n+2)/2⌋` edges that avoids every saturated planar graph on more than three vertices. It follows from the main theorem in four lines and is provided for reviewers who prefer a hypothesis-free statement.

[Adapters.lean](Erdos1019Planar/Adapters.lean) additionally checks that the hypothesis is satisfiable (`K₄` itself has `⌊16/4⌋ + ⌊5/2⌋ = 6` edges) and that every bipyramid is a saturated planar graph on more than three vertices; the main theorem does not depend on these consistency witnesses.

## Reproduce

Install Lean through elan, then run in this directory:

```sh
python3 fetch_sources.py
lake exe cache get
lake build
lake env lean Audit.lean
```

The exact Lean toolchain is pinned in [lean-toolchain](lean-toolchain): `leanprover/lean4:v4.34.0-rc1`. Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`, with transitive revisions in [lake-manifest.json](lake-manifest.json). The cache command is optional for correctness; it avoids rebuilding dependencies.

[Audit.lean](Audit.lean) restates the exact root statement as a typed `example` closed by the theorem and prints the axioms of the root, of the closed form, and of every named component. Every declaration depends exactly on `propext`, `Classical.choice`, and `Quot.sound`, the three standard foundational axioms of Lean's Mathlib; no other axiom, `sorry`, `admit`, `native_decide`, or custom trust extension occurs anywhere in the dependency cone. [verification.txt](verification.txt) records the local build and audit of this exported package. The published prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit by the designated verifiers and do not list the accepted foundational axioms; the three axioms above are stated here so that the audit can decide on them explicitly.

Local verification used cached upstream dependencies on arm64 macOS. It is not a clean, network-disabled rebuild or verification by two independent checker implementations. Authorized statement review, any required independent verification and permanent archival remain for the official review process.

## Attribution and submission status

The mathematical result is Simonovits's (PhD thesis; a proof is given by Stijn Cambie in the comments on the problem page). The Lean proof of the combinatorial core is by Codex and GPT-5.6 Sol in plby/lean-proofs, reused with full attribution. Its header says "Original license: Apache 2.0 … as described in the file LICENSE", but the package root `src/latest/LICENSE` of plby/lean-proofs at that commit is only a short pointer ("some files … from external sources") with no Apache text and no grant by a named copyright holder, so no explicit licence grant for the file is traceable; the file is therefore fetched at build time rather than redistributed, and this package makes no licence claim for it. The planarity definition, the straight-line-to-Jordan-arc bridge, the explicit plane embeddings of `K₄` and of every bipyramid, and the composed theorem were prepared with Claude Code (Claude Fable 5.1) assistance. The contribution sought is formalization of the exact problem statement with genuine planarity; no new mathematical discovery, first-formalization priority, or entitlement to an award is claimed. Please assess whether this implementation, together with the credited upstream proof, contributes eligible formalization work.

Proposed formalizer: `RECIPIENT-jsp-000849-cyr-A`, identity confirmation pending. No solver nomination, award tier, payment status or official verification status is asserted or changed. The `submissions/` location is proposed intake packaging; it is not a new official record schema. This is a self-submission with a direct interest in the review outcome.

Code and documentation follow the repository's respective [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT). The generated `Erdos1019Planar/Simonovits.lean` is fetched from its pinned public origin with unchanged authorship and is excluded from the repository archive; this package makes no license claim for it.
