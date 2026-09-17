import MerLeanExperiment.CocoloringAssembly
import MerLeanExperiment.NeighborhoodSplit
import MerLeanExperiment.RamseyReduction
import MerLeanExperiment.SmallCatalogData
import MerLeanExperiment.TriangleCycleSplit

noncomputable section

/-!
Structural reduction of the twelve-vertex four-cocoloring theorem to the 198
explicit neighborhood patterns selected by the `R(3,4)` catalogs.  This file
does not assume the universal twelve-vertex conclusion: its only remaining
premise names those concrete catalog patterns.
-/

namespace CochromaticTwenty

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

local instance {X : Type*} (K : SimpleGraph X) : DecidableRel K.Adj :=
  Classical.decRel _

/-- A graph isomorphism sends a finite clique to a clique of the same size. -/
theorem HasCliqueOfSize.map_iso {n : ℕ} (e : G ≃g H) :
    HasCliqueOfSize G n → HasCliqueOfSize H n := by
  classical
  rintro ⟨s, hcard, hs⟩
  let f : V ↪ W := e.toEquiv.toEmbedding
  refine ⟨s.map f, by simpa [f] using hcard, ?_⟩
  intro u hu v hv huv
  change u ∈ s.map f at hu
  change v ∈ s.map f at hv
  rw [Finset.mem_map] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  exact e.map_adj_iff.mpr
    (hs hu' hv' (fun h ↦ huv (congrArg e h)))

/-- A graph isomorphism sends a finite independent set to one of the same
size. -/
theorem HasIndependentOfSize.map_iso {n : ℕ} (e : G ≃g H) :
    HasIndependentOfSize G n → HasIndependentOfSize H n := by
  classical
  rintro ⟨s, hcard, hs⟩
  let f : V ↪ W := e.toEquiv.toEmbedding
  refine ⟨s.map f, by simpa [f] using hcard, ?_⟩
  intro u hu v hv huv hadj
  change u ∈ s.map f at hu
  change v ∈ s.map f at hv
  rw [Finset.mem_map] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  exact hs hu' hv' (fun h ↦ huv (congrArg e h))
    (e.map_adj_iff.mp hadj)

/-- Having no homogeneous four-set is invariant under graph isomorphism. -/
theorem noHomogeneousFour_iso_iff (e : G ≃g H) :
    NoHomogeneousFour G ↔ NoHomogeneousFour H := by
  constructor
  · intro hG
    exact ⟨fun h ↦ hG.1 (h.map_iso e.symm),
      fun h ↦ hG.2 (h.map_iso e.symm)⟩
  · intro hH
    exact ⟨fun h ↦ hH.1 (h.map_iso e),
      fun h ↦ hH.2 (h.map_iso e)⟩

/-- A complete `R(3,4)` catalog relabels every free graph of the indicated
finite cardinality to one of its listed graph codes. -/
theorem exists_catalog_iso_of_r34Free {n : ℕ} {codes : List ℕ}
    [Fintype V] (hcard : Fintype.card V = n) (hG : R34Free G)
    (hcomplete : CatalogComplete n codes) :
    ∃ code ∈ codes, Nonempty (G ≃g codeGraph n code) := by
  obtain ⟨code, hcode, ⟨e⟩⟩ :=
    hcomplete (G.overFin hcard) (hG.overFin hcard)
  exact ⟨code, hcode, ⟨(G.overFinIso hcard).trans e⟩⟩

/-- Catalog completeness plus the neighborhood split theorem normalizes a
chosen vertex of a graph with no homogeneous four-set to one exact catalog
pattern.  The statement is generic in the graph order and is also reusable
for the sixteen-vertex reduction. -/
theorem exists_neighborhoodPattern_iso_of_catalogs
    {n d : ℕ} {leftCodes rightCodes : List ℕ}
    (G : SimpleGraph (Fin n)) (hG : NoHomogeneousFour G) (v : Fin n)
    (hdegree : G.degree v = d) (hd : d < n)
    (hleftComplete : CatalogComplete d leftCodes)
    (hrightComplete : CatalogComplete (n - d - 1) rightCodes) :
    ∃ left ∈ leftCodes, ∃ right ∈ rightCodes, ∃ a : ℕ → Bool,
      Nonempty
        (G ≃g (neighborhoodPattern n d left right).graph a) := by
  classical
  have hleftCard : Fintype.card (G.neighborSet v) = d := by
    rw [SimpleGraph.card_neighborSet_eq_degree, hdegree]
  have hrightCard : Fintype.card ((Gᶜ).neighborSet v) = n - d - 1 := by
    rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.degree_compl,
      Fintype.card_fin, hdegree]
    omega
  obtain ⟨left, hleft, ⟨eLeft⟩⟩ := exists_catalog_iso_of_r34Free
    hleftCard (neighbor_induce_r34Free hG v) hleftComplete
  obtain ⟨right, hright, ⟨eRight⟩⟩ := exists_catalog_iso_of_r34Free
    hrightCard (nonneighbor_induce_compl_r34Free hG v) hrightComplete
  obtain ⟨a, he⟩ := exists_neighborhoodPattern_iso
    G v hd eLeft eRight
  exact ⟨left, hleft, right, hright, a, he⟩

/-- The exact 198 catalog-pattern obligations left by the structural
reduction: `3 × 3`, `6 × 9`, and `9 × 15`.  Each concrete theorem may use the
no-homogeneous-four hypothesis to discharge a coloring-or-forbidden
certificate. -/
def TwelveCatalogPatternsColorable : Prop :=
  (∀ left ∈ SmallCatalogData.catalog3,
    ∀ right ∈ SmallCatalogData.catalog8, ∀ a : ℕ → Bool,
      NoHomogeneousFour
          ((neighborhoodPattern 12 3 left right).graph a) →
        HasCocoloring ((neighborhoodPattern 12 3 left right).graph a) 4) ∧
  (∀ left ∈ SmallCatalogData.catalog4,
    ∀ right ∈ SmallCatalogData.catalog7, ∀ a : ℕ → Bool,
      NoHomogeneousFour
          ((neighborhoodPattern 12 4 left right).graph a) →
        HasCocoloring ((neighborhoodPattern 12 4 left right).graph a) 4) ∧
  (∀ left ∈ SmallCatalogData.catalog5,
    ∀ right ∈ SmallCatalogData.catalog6, ∀ a : ℕ → Bool,
      NoHomogeneousFour
          ((neighborhoodPattern 12 5 left right).graph a) →
        HasCocoloring ((neighborhoodPattern 12 5 left right).graph a) 4)

/-- On twelve vertices, an actual homogeneous four-set can be removed and
the remaining eight vertices use the universal three-cocoloring theorem. -/
theorem fin12_hasCocoloring_four_of_homogeneous_four
    (G : SimpleGraph (Fin 12))
    (hset : ∃ s : Finset (Fin 12),
      s.card = 4 ∧ Homogeneous G (s : Set (Fin 12))) :
    HasCocoloring G 4 :=
  hasCocoloring_four_of_exists_homogeneous_four (by simp)
    fin8_hasCocoloring_three hset

private theorem hasCocoloring_four_of_noHomogeneousFour
    (hpatterns : TwelveCatalogPatternsColorable)
    (G : SimpleGraph (Fin 12)) (hG : NoHomogeneousFour G) :
    HasCocoloring G 4 := by
  obtain ⟨H, hHG, hH, v, hv⟩ :=
    choose_degree_three_four_or_five_of_card_twelve (G := G) (by simp) hG
  have hHcolor : HasCocoloring H 4 := by
    rcases hv with hv | hv | hv
    · obtain ⟨left, hleft, right, hright, a, ⟨e⟩⟩ :=
        exists_neighborhoodPattern_iso_of_catalogs H hH v hv (by omega)
          SmallCatalogData.complete3 SmallCatalogData.complete8
      apply (hasCocoloring_iso_iff e).mpr
      exact hpatterns.1 left hleft right hright a
        ((noHomogeneousFour_iso_iff e).mp hH)
    · obtain ⟨left, hleft, right, hright, a, ⟨e⟩⟩ :=
        exists_neighborhoodPattern_iso_of_catalogs H hH v hv (by omega)
          SmallCatalogData.complete4 SmallCatalogData.complete7
      apply (hasCocoloring_iso_iff e).mpr
      exact hpatterns.2.1 left hleft right hright a
        ((noHomogeneousFour_iso_iff e).mp hH)
    · obtain ⟨left, hleft, right, hright, a, ⟨e⟩⟩ :=
        exists_neighborhoodPattern_iso_of_catalogs H hH v hv (by omega)
          SmallCatalogData.complete5 SmallCatalogData.complete6
      apply (hasCocoloring_iso_iff e).mpr
      exact hpatterns.2.2 left hleft right hright a
        ((noHomogeneousFour_iso_iff e).mp hH)
  rcases hHG with rfl | rfl
  · exact hHcolor
  · exact hasCocoloring_compl_iff.mp hHcolor

/-- Once the exact catalog-pattern obligations are discharged, every
ordinary graph on twelve vertices has a four-cocoloring.  If a homogeneous
four-set already exists, the result instead follows by removing it and using
the premise-free universal theorem on eight vertices. -/
theorem fin12_hasCocoloring_four_of_catalog_patterns
    (hpatterns : TwelveCatalogPatternsColorable)
    (G : SimpleGraph (Fin 12)) : HasCocoloring G 4 := by
  classical
  by_cases hG : NoHomogeneousFour G
  · exact hasCocoloring_four_of_noHomogeneousFour hpatterns G hG
  · have hlarge : HasCliqueOfSize G 4 ∨ HasIndependentOfSize G 4 := by
      unfold NoHomogeneousFour at hG
      tauto
    apply fin12_hasCocoloring_four_of_homogeneous_four
    rcases hlarge with ⟨s, hcard, hs⟩ | ⟨s, hcard, hs⟩
    · exact ⟨s, hcard, Or.inl hs⟩
    · exact ⟨s, hcard, Or.inr hs⟩

end CochromaticTwenty

#print axioms CochromaticTwenty.noHomogeneousFour_iso_iff
#print axioms CochromaticTwenty.exists_neighborhoodPattern_iso_of_catalogs
#print axioms CochromaticTwenty.fin12_hasCocoloring_four_of_catalog_patterns
