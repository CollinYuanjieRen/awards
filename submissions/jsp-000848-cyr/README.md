# JSP-000848 / Erdős 1018: bounded nonplanar subgraphs

This submission addresses the affirmative finite-graph statement: for every real ε > 0 there are natural numbers C and N such that every graph on n ≥ N vertices with at least n^(1+ε) edges has a subgraph with at most C vertices that admits no ordinary continuous crossing-free drawing in the Euclidean plane.

The root is `Erdos1018Topological.erdos_1018_ordinary_nonplanarity` in `MerLeanExperiment/Goal.lean`. Its nonplanarity conclusion is explicitly `¬ Nonempty (PlanarListColoring.PlaneDrawing S.coe)`. The definition of a drawing contains only vertex injection, continuous simple edge interiors, endpoints, vertex avoidance and noncrossing. There are no Euler, genus, subdivision-obstruction or coloring certificates in this definition.

## Proof and attribution

Kostochka and Pyber proved the underlying mathematical result in [*Small topological complete subgraphs of “dense” graphs*](https://doi.org/10.1007/BF02122555), Combinatorica 8 (1988), 83–86. The compact-K₅-subdivision construction is reused from the five-file plby Lean proof at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, credited to Codex and GPT-5.6 Sol. Its four auxiliary modules are unchanged; the root has only four import-prefix replacements.

The new work supplies the ordinary topological conclusion. Simple graph paths become arcs in the drawing. Distinct subdivision paths share no edge and meet geometrically only at common branch endpoints. Choosing parametrizations constructs an actual drawing of K₅. The ordinary-drawing Euler formula and face-boundary count give m + 6 ≤ 3n, contradicting m = 10 and n = 5. Applying this obstruction to the bounded compact subdivision proves the original eventual-in-n statement.

The complete natural-language proof of this added topological implication is in [Diestel, *Graph Theory*, second edition](https://www.maths.tcd.ie/EMIS/monographs/Diestel/en/GraphTheoryII.pdf), pp. 74–75, Theorem 4.2.7 and Corollaries 4.2.8–4.2.9. The original Kostochka–Pyber full text was not obtained in this campaign; its combinatorial theorem is reused as a complete checked Lean proof, not assumed from the literature.

The Euler/drawing machinery reuses JSP-000511 commit `566c5b9b083ebcdbe5e256ceb59f79472a36a41e`, including the ordinary drawing definition from plby Erdős 630 and the attributed Apache-2.0 Schoenflies development by Álvaro Begué at `05a43d29cde026618777db3d4e4316204ccca237`. Existing notices and applicable licenses are retained.

## Reproduce

The environment is pinned to Lean 4.34.0-rc1 and Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d`.

```sh
python3 fetch_sources.py
lake exe cache get
lake build
lake env lean Audit.lean
```

`fetch_sources.py` obtains the five external plby Erdős 1018 proof files at the pinned revision, checks their original SHA-256 hashes, performs the audited import-prefix replacements, then checks the resulting hashes. It preserves any locally changed file by failing. These originals are excluded from the submitted Git tree: the five files and repository README do not supply an explicit license grant, so this submission does not label them Apache-2.0. Their exact upstream links, hashes and attribution are in `external-proof-sources.json`.

## Verification scope

The exact submitted project passed a complete 8,837-job build and the full typed-root audit. Separate automated source-alignment and proof-completeness reviews passed. An independent traversal of 26,825 actual kernel declarations found only the three standard foundational axioms and excluded the old certificate-only nonplanarity predicate from the final root closure. [Verification instructions and receipts](verification/README.md) reproduce the successful comparison, axiom audit and Lean kernel replay.

No authoritative Erdős 1018 Lean target was found at the audited official/original-source repository snapshots. The independent frozen reference therefore uses the ordinary-drawing conclusion. The actual submitted proof export passed comparison of the complete target expression and definitions, actual axiom closure and Lean kernel replay. It is not an official-target comparator pass. Native macOS verification is unsandboxed and does not claim an independent external-kernel run.

The final root depends exactly on `propext`, `Classical.choice`, and `Quot.sound`, as recorded by [Audit.lean](Audit.lean) and [verification/receipt.json](verification/receipt.json). No custom axioms, proof holes, `native_decide`, or added original-problem conditions are used. The new proof modules are warning-free; reused modules retain upstream deprecation/style warnings. The audited public prize rules do not explicitly whitelist `propext`, `Classical.choice`, and `Quot.sound`; no official acceptance or award is claimed.
