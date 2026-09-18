import MerLeanExperiment.CocoloringAssembly

/-!
# Monotonicity of the cochromatic table in the number of vertices

Let `z(n)` be the maximum cochromatic number of a simple graph on `n`
vertices.  The whole published table `z(1..19)` is pinned down by a handful of
anchors together with the fact that `z` is monotone non-decreasing.  This file
supplies that monotonicity in both directions:

* `hasCocoloring_of_le` : a universal upper bound on `Fin n` gives the same
  upper bound on `Fin m` for every `m ≤ n` (so `z(m) ≤ z(n)`);
* `exists_not_hasCocoloring_of_le` : a lower-bound witness on `Fin m` gives a
  lower-bound witness on `Fin n` for every `n ≥ m`.

Both rest on `HasCocoloring.induce`: a cocoloring restricts to any induced
subgraph.
-/

namespace CochromaticTwenty

variable {V : Type*} {G : SimpleGraph V}

/-- A cocoloring restricts to every induced subgraph: colors the vertices of
`s` by their ambient colors, and each class is a subset of an ambient class. -/
theorem HasCocoloring.induce {k : ℕ} (s : Set V) :
    HasCocoloring G k → HasCocoloring (G.induce s) k := by
  rintro ⟨color, hcolor⟩
  exact ⟨fun v ↦ color (v : V), fun i ↦ homogeneous_induce_preimage (hcolor i)⟩

/-- Monotonicity of the table, upper direction: if every graph on `Fin n`
has a `k`-cocoloring and `m ≤ n`, then so does every graph on `Fin m`.
The graph on `Fin m` is pushed forward along `Fin.castLEEmb` and then
recovered as an induced subgraph of its image. -/
theorem hasCocoloring_of_le {m n k : ℕ} (hmn : m ≤ n)
    (h : ∀ H : SimpleGraph (Fin n), HasCocoloring H k)
    (G : SimpleGraph (Fin m)) : HasCocoloring G k := by
  classical
  let f : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hiso : G ≃g (G.map f).induce (Set.range f) := by
    refine ⟨Equiv.ofInjective f f.injective, ?_⟩
    intro u v
    simp [SimpleGraph.map_adj, Equiv.ofInjective, f.injective.eq_iff]
  exact (hasCocoloring_iso_iff hiso).mpr ((h (G.map f)).induce _)

/-- Monotonicity of the table, lower direction: a graph on `Fin m` without a
`k`-cocoloring produces a graph on `Fin n` without one, for every `n ≥ m`. -/
theorem exists_not_hasCocoloring_of_le {m n k : ℕ} (hmn : m ≤ n)
    (G : SimpleGraph (Fin m)) (hG : ¬ HasCocoloring G k) :
    ∃ H : SimpleGraph (Fin n), ¬ HasCocoloring H k := by
  by_contra hc
  exact hG (hasCocoloring_of_le hmn
    (fun H ↦ not_not.mp (fun hH ↦ hc ⟨H, hH⟩)) G)

end CochromaticTwenty

#print axioms CochromaticTwenty.HasCocoloring.induce
#print axioms CochromaticTwenty.hasCocoloring_of_le
#print axioms CochromaticTwenty.exists_not_hasCocoloring_of_le
