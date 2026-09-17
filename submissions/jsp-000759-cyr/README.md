# JSP-000759 (Erdős #915): the Bollobás–Erdős question on `m` disjoint paths, both readings

Catalog entry: [JSP-000759](../../problems/catalog-0701-0800.md#JSP-000759). Problem page:
<https://www.erdosproblems.com/915>.

## The question and its complete answer

Bollobás and Erdős (1962) asked: let `G` be a graph with `1 + n(m−1)` vertices and
`1 + n·C(m,2)` edges. Must `G` contain two vertices connected by `m` disjoint paths? As the
problem page notes, "disjoint" may mean *internally vertex-disjoint* or *edge-disjoint*, and the
two readings have different answers. Everything below is proved in Lean 4 / Mathlib, for every
`m` and every `n`, with only the three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`):

| face | statement | theorem |
|---|---|---|
| (i) | vertex-disjoint reading, `m = 2, 3, 4`: **yes** | `Erdos915.vertex_rails_of_le_four` |
| (ii) | vertex-disjoint reading, every `m ≥ 5`: **no** — an explicit graph with exactly `1 + n(m−1)` vertices and `1 + n·C(m,2)` edges and no two vertices joined by `m` internally disjoint paths | `Erdos915.exists_no_vertex_rails_of_ge_five` |
| (iii) | Mader's theorem: `N ≥ m` and `2|E| + e₀ + ⋯ + e_{m−2} > m(N−1)` force `m` edge-disjoint paths | `Erdos915.mader_edge_rails` |
| (iv) | edge-disjoint reading, every `m ≥ 2`: **yes** | `Erdos915.edge_rails_of_bollobas_erdos` |
| (v) | `ℓ_m(N) = ⌊m(N−1)/2⌋ + 1` for `2 ≤ m ≤ N` (`IsLeast` form) | `Erdos915.edgeRailNumber_eq` |

All five are bundled as `Erdos915.erdos_915` in [MerLeanExperiment/Main.lean](MerLeanExperiment/Main.lean).
The definitions ([MerLeanExperiment/Defs.lean](MerLeanExperiment/Defs.lean)) are the literal
ones: `HasVertexRails G m` is the existence of two distinct vertices and an injective family of
`m` paths between them, pairwise sharing no vertex other than the endpoints; `HasEdgeRails G m`
the same with pairwise edge-disjointness; `lowDegreeCount G r = e_r(G)` is the number of vertices
of degree at most `r`. The frozen faces are stated once more, with `sorry`, in
[MerLeanExperiment/Target.lean](MerLeanExperiment/Target.lean), which nothing imports; it serves
as the challenge file for statement comparison.

Two side conditions are part of the mathematics and are stated explicitly: Mader's Satz 1 has the
hypothesis `N ≥ m` (his `e(G) ≥ n`), which the problem page omits and without which the
inequality-only statement is false (`K₃`, `m = 5`); likewise `ℓ_m(N) = ⌊m(N−1)/2⌋+1` is stated for
`m ≤ N` (for `N < m` the least-element set is vacuous above `C(N,2)`). Neither restricts the
Bollobás–Erdős question, where `N = 1 + n(m−1) ≥ m`.

## Proof structure

* [RailsTwo.lean](MerLeanExperiment/RailsTwo.lean): `m = 2` — `|E| ≥ |V|` forces a cycle, whose
  two arcs are the paths; vertex rails are edge rails.
* [RailsThree.lean](MerLeanExperiment/RailsThree.lean): `m = 3` (Bártfai 1960): a spanning forest,
  its fundamental cycles, two cycles sharing an edge, hence a theta subgraph.
* [RailsFour.lean](MerLeanExperiment/RailsFour.lean): `m = 4` (Bollobás 1966, `k₄(N) = 2N−1` for
  `N ≥ 4`). The Lean proof establishes Bollobás's part (a) by an induction on the support size with
  the sharp invariant `|E| + 2 ≤ 2N` for graphs without a 4-rail; unlike the published proof it does
  not go through his structure theorem (b) (wheels and `H^N`-graphs), which is not reproduced here.
* [EdgeMenger.lean](MerLeanExperiment/EdgeMenger.lean): the edge form of Menger's theorem
  (absent from Mathlib), proved by Ford–Fulkerson with unit capacities and flow decomposition,
  connected to Mathlib's `SimpleGraph.IsEdgeReachable`.
* [MaderTheorem.lean](MerLeanExperiment/MaderTheorem.lean): Mader's Satz 1 (Math. Z. 131, 1973).
  The induction on the number of vertices follows Mader (a minimum cut, the two sides, one side
  contracted to an apex, degree bookkeeping); his path surgery for the contraction step is replaced
  by an uncrossing argument using submodularity of cut sizes. Menger is used once, at the end.
* [MaderCorollary.lean](MerLeanExperiment/MaderCorollary.lean): the Bollobás–Erdős case and the
  exact value `ℓ_m(N)`, with the sharpness graph (a universal hub joined to a circulant-plus-matching
  rim; Leonard's "bi-wheel").
* [CounterexampleFive.lean](MerLeanExperiment/CounterexampleFive.lean): `m = 5`, `n = 4`: the
  17-vertex, 41-edge graph of Sørensen–Thomassen (`k₅(17) = 42`), with kernel-checked separator
  certificates.
* [MaderDisproof.lean](MerLeanExperiment/MaderDisproof.lean): every `m ≥ 6`: an explicit graph in
  the spirit of Mader's construction (Math. Z. 131, p. 229: an apex, two blocking vertices, a clique
  with attached near-complete blocks), engineered so that its vertex and edge counts equal
  `1 + n(m−1)` and `1 + n·C(m,2)` exactly (with `n = m−1`); it is not Mader's literal graph. Two
  separators of size `m−2` show that no pair of vertices has `m` internally disjoint paths.
* [VertexRailsLeFour.lean](MerLeanExperiment/VertexRailsLeFour.lean), [Main.lean](MerLeanExperiment/Main.lean): assembly.

No `sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration occurs anywhere outside
the challenge file `Target.lean`; finite certificates use kernel `decide` on `Fin 17`.

## Reproduce

```bash
cd submissions/jsp-000759-cyr
lake exe cache get
lake build
lake env lean MerLeanExperiment/Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib pinned to
`1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in
[lake-manifest.json](lake-manifest.json). The expected audit output is in
[verification.txt](verification.txt): every listed theorem depends on exactly
`[propext, Classical.choice, Quot.sound]`.

## Attribution and submission status

The mathematics is due to A. Bártfai (Mat. Lapok 11, 1960, `k₃`), B. Bollobás (Studia Sci. Math.
Hungar. 1, 1966, `k₄`), W. Mader ("Ein Extremalproblem des Zusammenhangs von Graphen", Math. Z.
131, 1973: the edge-disjoint theorem, the value of `ℓ_m`, and the disproof of the vertex-disjoint
conjecture for `m ≥ 5`), B. A. Sørensen and C. Thomassen (J. Combin. Theory Ser. B 17, 1974, the
`m = 5` witness) and J. L. Leonard (1972–73); the question is from B. Bollobás and P. Erdős
(Mat. Lapok 13, 1962). None of these papers is used as an assumption; where the Lean argument
departs from the published route this is stated above.

Prior Lean work on this entry: the third-party module `Erdos915` in
[plby/lean-proofs](https://github.com/plby/lean-proofs) (Apache License 2.0), and the upstream
submissions [PR #739](https://github.com/TheJustinSunPrize/awards/pull/739),
[PR #753](https://github.com/TheJustinSunPrize/awards/pull/753) and
[issue #686](https://github.com/TheJustinSunPrize/awards/issues/686), each formalize the `m = 5`
vertex-disjoint counterexample only. The adjacency list of the 17-vertex graph and the
three-separator strategy in `CounterexampleFive.lean` follow plby's `Erdos915` and PR #739 (credited
in the file header) and were independently re-verified; every other module is new. This submission
claims the complete answer to the catalog question (both readings, all `m`), not the `m = 5`
counterexample alone.

The Lean code was prepared by Collin Yuanjie Ren (@CollinYuanjieRen) with Claude Code (Claude
Fable 5.1 and Claude Opus) assistance. Code and documentation follow the repository's respective
[code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
