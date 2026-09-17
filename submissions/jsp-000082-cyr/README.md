# JSP-000082: Erdős #64, an infinite tree of minimum degree `3`

This package submits, for intake and eligibility review, a Lean proof of a remark recorded on the page of [JSP-000082](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0001-0100.md#JSP-000082) / [Erdős Problem #64](https://www.erdosproblems.com/64): does every finite graph with minimum degree at least `3` contain a cycle of length `2^k` for some `k ≥ 2`?

**Scope statement.** The question for finite graphs is open and is not addressed, nor are the Liu–Montgomery results. The problem page records: "An infinite tree with minimum degree `3` shows that the answer is trivially false for infinite graphs." This package proves that remark with an explicit infinite tree: the ternary tree on `ℕ` in which `v` is adjacent to its children `3v + 1, 3v + 2, 3v + 3` and (for `v ≥ 1`) to its parent. Every vertex has a finite set of at least three neighbours, the graph is acyclic, and hence it has no cycle of length `2^k` for any `k`; the cycle condition is written in the shape of the formal-conjectures statement `Erdos64.erdos_64` (which quantifies over finite graphs only), and the construction and the degree formulation (explicit finite neighbour sets, avoiding finiteness instances) are ours.

## Statement and proof

[Erdos64InfiniteTree/Main.lean](Erdos64InfiniteTree/Main.lean) defines `ternaryAdj` / `ternaryTree : SimpleGraph ℕ` and proves

```lean
theorem ternaryTree_neighbors (v : ℕ) :
    ∃ s : Finset ℕ, (∀ w, ternaryTree.Adj v w ↔ w ∈ s) ∧ 3 ≤ s.card
theorem ternaryTree_isAcyclic : ternaryTree.IsAcyclic
theorem erdos_64_infinite_counterexample :
    ∃ (V : Type) (G : SimpleGraph V), Infinite V ∧
      (∀ v : V, ∃ s : Finset V, (∀ w, G.Adj v w ↔ w ∈ s) ∧ 3 ≤ s.card) ∧
      G.IsAcyclic ∧
      ¬ ∃ (k : ℕ) (v : V) (c : G.Walk v v), k ≥ 2 ∧ c.IsCycle ∧ c.length = 2 ^ k
```

Proof. The neighbours of `v` are `3v + 1, 3v + 2, 3v + 3` and, for `v ≥ 1`, `(v − 1)/3`. If there were a cycle, rotate it to start at its largest vertex `u`; both walk-neighbours of `u` are smaller neighbours, hence both equal the parent `(u − 1)/3`, contradicting that the second and penultimate vertices of a cycle differ.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Toolchain `leanprover/lean4:v4.34.0-rc1` ([lean-toolchain](lean-toolchain)); Mathlib `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in [lake-manifest.json](lake-manifest.json). [Audit.lean](Audit.lean) restates the theorem as a typed `example` and prints the axioms: exactly `propext`, `Classical.choice`, `Quot.sound`. [verification.txt](verification.txt) records the local build and audit. The prize rules (v1.0, 16 September 2026, section 6) require an offline axiom audit and do not enumerate accepted foundational axioms; the three are stated here explicitly. Local verification used cached upstream dependencies on arm64 macOS and is not an official attestation.
