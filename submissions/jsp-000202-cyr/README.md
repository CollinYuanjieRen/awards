# JSP-000202: the Hopf–Pannwitz planar diameter theorem f₂(n) = n (Erdős #223)

This package submits a Lean formalization for intake and eligibility review of the planar case of [JSP-000202](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0201-0300.md#JSP-000202) (Erdős Problem [#223](https://www.erdosproblems.com/223), the Vázsonyi / Hopf–Pannwitz problem): among `n` points in the plane of diameter `1`, how many pairs can be at distance exactly `1` (the diameter)? Hopf and Pannwitz (1934) proved the answer is `f₂(n) = n`, via the elegant argument Erdős describes in [Er46b].

This package formalizes that complete planar theorem, both directions, for all `n ≥ 3`. **Higher dimensions are out of scope** (the page also records `f₃(n) = 2n − 2` and Erdős's `d ≥ 4` formula; none of those is claimed here).

## Statement

Model `n` points as `P : Fin n → EuclideanSpace ℝ (Fin 2)` and form the *diameter graph* whose edges join the pairs at the extremal distance `D`:

```lean
def diameterGraph (P : Fin n → EuclideanSpace ℝ (Fin 2)) (D : ℝ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ dist (P i) (P j) = D
def diameterPairCounts (n : ℕ) : Set ℕ :=
  {c | ∃ P D, Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧ (diameterGraph P D).edgeFinset.card = c}
```

The main theorem (`Jsp202/Main.lean`) is

```lean
theorem hopf_pannwitz (n : ℕ) (hn : 3 ≤ n) : IsGreatest (diameterPairCounts n) n
```

i.e. `n` pairs at the diameter are realizable and no configuration realizes more. It is assembled from the two directions:

```lean
theorem hopf_pannwitz_upper (n : ℕ) (P : Fin n → EuclideanSpace ℝ (Fin 2))
    (hinj : Function.Injective P) (D : ℝ) (hUB : ∀ i j, dist (P i) (P j) ≤ D) :
    (diameterGraph P D).edgeFinset.card ≤ n
theorem exists_n_diameter_pairs (n : ℕ) (hn : 3 ≤ n) :
    ∃ P D, Function.Injective P ∧ (∀ i j, dist (P i) (P j) ≤ D) ∧ (diameterGraph P D).edgeFinset.card = n
```

## Proof

The upper bound `≤ n` is the substantive direction. Its geometric heart is the **crossing lemma** (`Jsp202/CrossingLemma.lean`): four distinct points with all pairwise distances `≤ D` and two of the pairs at distance exactly `D` have their two segments meeting. We prove it via Radon's partition theorem (`Convex.radon_partition`): the four coplanar points admit a Radon partition, and every partition shape (opposite pair, diagonal pair, or singleton) yields a common point, using that equality in the triangle inequality characterizes betweenness in the strictly convex plane. From the crossing lemma, any two edges of the diameter graph meet (`every_two_edges_meet`), and a vertex of degree `≥ 3` has an angularly-middle neighbour of degree `1` (`middle_neighbour`, via a `≤ 60°`-cone / law-of-cosines argument); a vertex-deletion induction then gives `≤ n` (`Jsp202/UpperBound.lean`). The lower bound places vertex `0` at the origin and the others on a `≤ 60°` arc of the unit circle, so the only distance-`1` pairs are the `n − 1` radii plus one arc chord — exactly `n` (`Jsp202/ConstructionGeneral.lean`; the fixed cases `f2_three/four/five` in `Jsp202/Construction.lean` are explicit instances).

`Challenge.lean` is a comparator-style challenge module (the same Mathlib-only definitions and `hopf_pannwitz` with `sorry`, not imported by the build) for mechanical statement comparison. The source statement (erdosproblems.com/223, retrieved 2026-09-16) is recorded verbatim in `sources/erdos223-statement.txt` with its SHA-256 in `verification.txt`.

## Reproduce

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean toolchain `leanprover/lean4:v4.34.0-rc1`; Mathlib pinned to `1fe0a51a5ecdee23c424b6e29ecb1d40eb35316d` with transitive revisions in `lake-manifest.json`. `Audit.lean` prints the axioms of `hopf_pannwitz` and its components: `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, custom axioms, `native_decide`, `opaque`/`unsafe`/`implemented_by` declarations occur in the built library (`Jsp202/`, `Jsp202.lean`, `Audit.lean`); the only `sorry` in the package is the single statement-only target of `Challenge.lean`. `verification.txt` records the local build and audit of this exported package.

## Attribution, prior art, and submission status

The theorem is Hopf and Pannwitz's (1934). **Prior art:** an independent Lean 4 formalization of Erdős #223 exists in the public third-party repository plby/lean-proofs (`ErdosProblems/Erdos223.lean`, covering the planar case and higher dimensions); this package was authored independently, without reading or copying that source, and proves the planar theorem on its own definitions and via a different (Radon-partition) route for the crossing lemma. Prepared with Claude (Anthropic) assistance (design, proof-route reconstruction, and hints by Claude Fable 5.1; Lean implementation by Claude Opus subagents) and locally checked; an independent adversarial audit of the package passed. No first-formalization priority or entitlement to an award is claimed; this is a self-submission with a direct interest in the review outcome. Proposed formalizer: `RECIPIENT-jsp-000202-cyr-A`, identity confirmation pending. Code and documentation follow the repository's [code license](../../LICENSE) and [content license](../../LICENSE-CONTENT).
