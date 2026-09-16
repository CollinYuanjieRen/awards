# JSP-000511 / Erdős 630: planar bipartite list coloring

This formalizes the finite-graph Alon–Tarsi theorem: every planar bipartite graph is colorable from arbitrary three-element lists at its vertices. The planarity hypothesis is an ordinary continuous crossing-free drawing in the Euclidean plane. Euler identities, edge bounds, orientations, and coloring certificates are proved internally.

The primary theorem is `PlanarListColoring.planar_bipartite_three_list_colorable` in [Goal.lean](MerLeanExperiment/Goal.lean). Its exact hypotheses are a finite simple graph, existence of an ordinary `PlaneDrawing`, bipartiteness, and three-element vertex lists of natural-number colors. [ArbitraryPalette.lean](MerLeanExperiment/ArbitraryPalette.lean) proves the corresponding theorem for every color type `C`, without requiring that `C` be finite, countable, or inhabited. Empty graphs, isolated vertices, disconnected graphs, and bridges are included.

## Drawing and proof

[PlaneDrawing.lean](MerLeanExperiment/PlaneDrawing.lean) requires injective vertex placement, continuous simple edge interiors, correct endpoints, avoidance of vertices by edge interiors, and disjoint interiors of distinct edges. [DrawingAdapter.lean](MerLeanExperiment/DrawingAdapter.lean) realizes the independently defined standard graph-drawing interface from these data.

Polygonal redrawing and cycle-and-ear induction construct an enumeration of actual complementary faces. Exact face replacement proves Euler's equality and the twice-per-edge boundary sum. Bipartiteness and simplicity imply that each face boundary has at least four edges. Induction through separators of size at most one extends the edge bound to arbitrary finite graphs. Restricting to each selected edge family and exactly its incident vertices supplies Hall's orientation criterion. The attributed bipartite-kernel argument then supplies list coloring.

## Reproduce

Lean is pinned to `4.34.0-rc1`; Mathlib is pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`. From this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The default target includes both final theorems. [Audit.lean](Audit.lean) checks their complete types and prints their actual axiom dependencies. Both depend exactly on `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, proof hole, external oracle, or `native_decide` is used. The new proof modules build without warnings; the attributed vendored topology modules retain upstream deprecation/style warnings.

[Verification instructions](verification/README.md) provide the pinned comparator-based driver, its negative tests, and the independent frozen target. The driver compares the full target expression and all its definition dependencies with no definition/theorem exceptions, audits the actual proof's axioms, and replays the exported environments through Lean's kernel.

There is no Formal Conjectures Erdős 630 module at the audited snapshot `40e7c98697de6f66b8cbdbf641749ab39ed9c152`. This is therefore a comparison with the independently reviewed, frozen ordinary-drawing statement. The recorded native macOS run does not claim sandbox isolation or an independent external kernel. Public prize rules require axiom and statement audits but do not publish a whitelist explicitly approving the three standard axioms. These checks establish the reported proof results, not prize approval or a completed award-verification record.

## Attribution

- Noga Alon and Michael Tarsi, *Colorings and orientations of graphs*, Combinatorica 12 (1992), 125–134, Corollary 3.4. [Author-hosted paper](https://www.tau.ac.il/~nogaa/PDFS/chrom3.pdf).
- [plby/lean-proofs](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos630.lean), commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, Apache 2.0: ordinary drawing definition and orientation/kernel/list-coloring formalization, retaining the original formal authors' headers. Its existing `IsPlanar` bundles Euler/face certificates; the present proof constructs the missing topological-to-combinatorial input from the ordinary drawing.
- Álvaro Begué, [schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean/tree/05a43d29cde026618777db3d4e4316204ccca237), commit `05a43d29cde026618777db3d4e4316204ccca237`, Apache 2.0: plane topology and redrawing. The 52-file import closure is vendored with original headers and a small Mathlib compatibility port.
- Lean FRO's [comparator](https://github.com/leanprover/comparator/tree/011e9d35a10a054ed4b66d8379115ad870f2b0ce), Apache 2.0, supplies comparison, axiom-traversal, and replay APIs used by the verification driver.

The new formal work constructs the ordinary-drawing adapter, exact crosscut components and face counts, Euler identities, separator counts, endpoint-density bridge, and final composition. This is a formalization of a known theorem, with the prior mathematical and formal work credited above.
