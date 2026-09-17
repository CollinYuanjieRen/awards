import MerLeanExperiment.TwelveColoringReduction
import MerLeanExperiment.CoreWitnesses

namespace CochromaticTwenty

/-- Complement the source and target of an actual graph isomorphism. -/
def graphIsoComplement {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    change (e u ≠ e v ∧ ¬ H.Adj (e u) (e v)) ↔ (u ≠ v ∧ ¬ G.Adj u v)
    rw [e.injective.ne_iff, e.map_rel_iff]

def SixteenCatalogPatternsClassified : Prop :=
  ∀ left ∈ SmallCatalogData.catalog7, ∀ right ∈ SmallCatalogData.catalog8,
    ∀ a : ℕ → Bool, NoHomogeneousFour ((neighborhoodPattern 16 7 left right).graph a) →
      Nonempty ((neighborhoodPattern 16 7 left right).graph a ≃g codeGraph 16 coreCode0) ∨
      Nonempty ((neighborhoodPattern 16 7 left right).graph a ≃g codeGraph 16 coreCode1)

theorem sixteen_classification_of_catalog_patterns
    (hpatterns : SixteenCatalogPatternsClassified)
    (G : SimpleGraph (Fin 16)) (hG : NoHomogeneousFour G) :
    Nonempty (G ≃g codeGraph 16 coreCode0) ∨
      Nonempty (G ≃g codeGraph 16 coreCode1) := by
  classical
  obtain ⟨H, hH, hno, v, hdegree⟩ :=
    choose_degree_seven_of_card_sixteen (by simp) hG
  obtain ⟨left, hl, right, hr, a, ⟨e⟩⟩ :=
    exists_neighborhoodPattern_iso_of_catalogs H hno v hdegree (by decide)
      SmallCatalogData.complete7 SmallCatalogData.complete8
  have hc := hpatterns left hl right hr a ((noHomogeneousFour_iso_iff e).mp hno)
  have hcores : Nonempty (H ≃g codeGraph 16 coreCode0) ∨
      Nonempty (H ≃g codeGraph 16 coreCode1) := by
    rcases hc with hf | hf
    · exact Or.inl ⟨e.trans (Classical.choice hf)⟩
    · exact Or.inr ⟨e.trans (Classical.choice hf)⟩
  rcases hH with rfl | rfl
  · exact hcores
  · rcases hcores with hf | hf
    · left
      have ecomp := (graphIsoComplement (Classical.choice hf)).trans CoreWitnesses.complement0_iso
      simpa using (show Nonempty (Gᶜᶜ ≃g codeGraph 16 coreCode0) from ⟨ecomp⟩)
    · right
      have ecomp := (graphIsoComplement (Classical.choice hf)).trans CoreWitnesses.complement1_iso
      simpa using (show Nonempty (Gᶜᶜ ≃g codeGraph 16 coreCode1) from ⟨ecomp⟩)

end CochromaticTwenty
#print axioms CochromaticTwenty.sixteen_classification_of_catalog_patterns
