import MerLeanExperiment.ModelAdapters
import MerLeanExperiment.Twelve

/-!
# The lower anchors of the cochromatic table

Explicit witnesses showing that the published values of `z(1..19)` cannot be
lowered, for every anchor except `z(9) ≥ 4` (which needs the nine-vertex graph
of `MerLeanExperiment.NineLowerBound`):

* `fin1_not_hasCocoloring_zero` : `z(1) ≥ 1`, since zero colors color nothing;
* `fin3_not_hasCocoloring_one`  : `z(3) ≥ 2`, witnessed by a single edge plus
  an isolated vertex;
* `fin5_not_hasCocoloring_two`  : `z(5) ≥ 3`, witnessed by the five-cycle,
  whose largest homogeneous set has two vertices;
* `paley17_prefix_not_hasCocoloring` : a generic counting bound for the Paley
  graph of order seventeen restricted to its first `m` vertices, giving
  `z(13) ≥ 5` and `z(16) ≥ 6`.

The generic Paley bound is a pigeonhole argument: `k` color classes on `m`
vertices with `3 * k < m` force a class of at least four vertices, and
`paley17_no_homogeneous_four` says the Paley graph has no homogeneous
four-set.  `paley17OnTwelve_not_hasCocoloring_three` of
`MerLeanExperiment.Twelve` is the `m = 12`, `k = 3` instance; that file is
left untouched and the instance is recorded here as
`paley17OnTwelve_not_hasCocoloring_three_of_prefix`.
-/

namespace CochromaticTwenty

/-- A homogeneous set of a comapped graph maps forward to a homogeneous set. -/
theorem homogeneous_comap_image {V W : Type*} {H : SimpleGraph W} {f : V → W}
    {s : Set V} (hs : Homogeneous (H.comap f) s) : Homogeneous H (f '' s) := by
  rcases hs with h | h
  · exact Or.inl (Set.Pairwise.image (fun u hu v hv huv ↦ h hu hv huv))
  · exact Or.inr (Set.Pairwise.image (fun u hu v hv huv ↦ h hu hv huv))

/-- `z(1) ≥ 1`: zero colors cannot color a single vertex. -/
theorem fin1_not_hasCocoloring_zero (G : SimpleGraph (Fin 1)) :
    ¬ HasCocoloring G 0 := by
  rintro ⟨c, -⟩; exact (c 0).elim0

/-- Existential form of `fin1_not_hasCocoloring_zero`. -/
theorem exists_fin1_not_hasCocoloring_zero :
    ∃ G : SimpleGraph (Fin 1), ¬ HasCocoloring G 0 :=
  ⟨⊥, fin1_not_hasCocoloring_zero ⊥⟩

/-- Boolean adjacency of the single edge `0 — 1` on three vertices. -/
private def adj3 (u v : Fin 3) : Bool :=
  (u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 0)

/-- The three-vertex witness for `z(3) ≥ 2`: one edge `0 — 1` and an isolated
vertex `2`.  Its three vertices are neither a clique nor an independent set. -/
def G3 : SimpleGraph (Fin 3) where
  Adj u v := adj3 u v
  symm.symm := by decide
  loopless.irrefl := by decide

/-- Adjacency in `G3` is decidable. -/
instance : DecidableRel G3.Adj := fun a b ↦ by
  change Decidable (adj3 a b = true); infer_instance

/-- `z(3) ≥ 2`: one color would make all three vertices homogeneous, but
`0 — 1` is an edge and `0 — 2` is not. -/
theorem fin3_not_hasCocoloring_one : ¬ HasCocoloring G3 1 := by
  rintro ⟨c, hc⟩
  have huniv : {v : Fin 3 | c v = 0} = Set.univ := by
    ext v; simp [Subsingleton.elim (c v) 0]
  have h : Homogeneous G3 {v : Fin 3 | c v = 0} := by
    have := hc 0
    simpa [Subsingleton.elim (0 : Fin 1) 0] using this
  rw [huniv] at h
  rcases h with h | h
  · exact absurd (h (Set.mem_univ 0) (Set.mem_univ 2) (by decide)) (by decide)
  · exact absurd (h (Set.mem_univ 0) (Set.mem_univ 1) (by decide)) (by decide)

/-- Boolean adjacency of the five-cycle `0-1-2-3-4-0`. -/
private def adjC5 (u v : Fin 5) : Bool :=
  ((u.val + 1) % 5 == v.val) || ((v.val + 1) % 5 == u.val)

/-- The five-cycle `0-1-2-3-4-0`, the witness for `z(5) ≥ 3`. -/
def C5 : SimpleGraph (Fin 5) where
  Adj u v := adjC5 u v
  symm.symm := by decide
  loopless.irrefl := by decide

/-- Adjacency in `C5` is decidable. -/
instance : DecidableRel C5.Adj := fun a b ↦ by
  change Decidable (adjC5 a b = true); infer_instance

/-- The five-cycle has no homogeneous triple: three vertices always contain
both an edge and a non-edge. -/
theorem c5_no_homogeneous_three (s : Finset (Fin 5)) (hs : s.card = 3) :
    ¬ Homogeneous C5 (s : Set (Fin 5)) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have key : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ¬ ((C5.Adj a b ∧ C5.Adj a c ∧ C5.Adj b c) ∨
          (¬ C5.Adj a b ∧ ¬ C5.Adj a c ∧ ¬ C5.Adj b c)) := by decide
  intro hhom
  apply key a b c hab hac hbc
  rcases hhom with h | h
  · exact Or.inl ⟨h (by simp) (by simp) hab, h (by simp) (by simp) hac,
      h (by simp) (by simp) hbc⟩
  · exact Or.inr ⟨h (by simp) (by simp) hab, h (by simp) (by simp) hac,
      h (by simp) (by simp) hbc⟩

/-- `z(5) ≥ 3`: two colors on five vertices leave a class of three vertices,
and the five-cycle has no homogeneous triple. -/
theorem fin5_not_hasCocoloring_two : ¬ HasCocoloring C5 2 := by
  classical
  rintro ⟨color, hcolor⟩
  obtain ⟨i, hi⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card color (n := 2) (by simp)
  obtain ⟨s, hs, hscard⟩ :=
    Finset.exists_subset_card_eq (show 3 ≤ (Finset.univ.filter fun v ↦ color v = i).card by omega)
  refine c5_no_homogeneous_three s hscard (homogeneous_mono ?_ (hcolor i))
  intro v hv
  have := hs (by simpa using hv)
  simpa using (Finset.mem_filter.mp this).2

/-- Generic Paley lower bound: the Paley graph of order seventeen restricted
to its first `m` vertices has no `k`-cocoloring whenever `3 * k < m`.  Indeed
some color class would then have four vertices, and `paley17` has no
homogeneous four-set. -/
theorem paley17_prefix_not_hasCocoloring (m k : ℕ) (hm : m ≤ 17) (h : 3 * k < m) :
    ¬ HasCocoloring (paley17.comap (Fin.castLEEmb hm)) k := by
  classical
  rintro ⟨color, hcolor⟩
  have hcard : Fintype.card (Fin k) * 3 < Fintype.card (Fin m) := by
    simpa using (by omega : k * 3 < m)
  obtain ⟨i, hi⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card color (n := 3) hcard
  obtain ⟨s, hs, hscard⟩ :=
    Finset.exists_subset_card_eq (show 4 ≤ (Finset.univ.filter fun v ↦ color v = i).card by omega)
  have hhom : Homogeneous paley17
      ((s.map (Fin.castLEEmb hm) : Finset (Fin 17)) : Set (Fin 17)) := by
    have h1 : Homogeneous (paley17.comap (Fin.castLEEmb hm)) (s : Set (Fin m)) :=
      homogeneous_mono (fun v hv ↦ by
        have := hs (by simpa using hv)
        simpa using (Finset.mem_filter.mp this).2) (hcolor i)
    have h2 := homogeneous_comap_image h1
    convert h2 using 1
    ext w; simp
  exact paley17_no_homogeneous_four _ (by simpa using hscard) hhom

/-- `z(13) ≥ 5`: four colors do not suffice on the first thirteen vertices of
the Paley graph of order seventeen. -/
theorem fin13_not_hasCocoloring_four :
    ¬ HasCocoloring (paley17.comap (Fin.castLEEmb (by omega : 13 ≤ 17))) 4 :=
  paley17_prefix_not_hasCocoloring 13 4 _ (by omega)

/-- `z(16) ≥ 6`: five colors do not suffice on the first sixteen vertices of
the Paley graph of order seventeen. -/
theorem fin16_not_hasCocoloring_five :
    ¬ HasCocoloring (paley17.comap (Fin.castLEEmb (by omega : 16 ≤ 17))) 5 :=
  paley17_prefix_not_hasCocoloring 16 5 _ (by omega)

/-- `z(12) ≥ 4`, already proved in `MerLeanExperiment.Twelve`, is the
`m = 12`, `k = 3` instance of the generic Paley bound. -/
theorem paley17OnTwelve_not_hasCocoloring_three_of_prefix :
    ¬ HasCocoloring paley17OnTwelve 3 :=
  paley17_prefix_not_hasCocoloring 12 3 (by omega) (by omega)

end CochromaticTwenty

#print axioms CochromaticTwenty.fin1_not_hasCocoloring_zero
#print axioms CochromaticTwenty.fin3_not_hasCocoloring_one
#print axioms CochromaticTwenty.fin5_not_hasCocoloring_two
#print axioms CochromaticTwenty.paley17_prefix_not_hasCocoloring
#print axioms CochromaticTwenty.fin13_not_hasCocoloring_four
#print axioms CochromaticTwenty.fin16_not_hasCocoloring_five
#print axioms CochromaticTwenty.paley17OnTwelve_not_hasCocoloring_three_of_prefix
