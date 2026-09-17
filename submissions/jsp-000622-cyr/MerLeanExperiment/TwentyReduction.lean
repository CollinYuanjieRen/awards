import MerLeanExperiment.TwoFoursTransport
import MerLeanExperiment.SixteenClassificationReduction

namespace CochromaticTwenty

def SixteenGraphsClassified : Prop :=
  ∀ G : SimpleGraph (Fin 16), NoHomogeneousFour G →
    Nonempty (G ≃g codeGraph 16 coreCode0) ∨ Nonempty (G ≃g codeGraph 16 coreCode1)

def FixedCoresHaveTwoFours : Prop :=
  (∀ a : ℕ → Bool, TwoHomogeneousFours ((fixedCorePattern coreCode0).graph a)) ∧
  (∀ a : ℕ → Bool, TwoHomogeneousFours ((fixedCorePattern coreCode1).graph a))

/-- Structural twenty-vertex reduction with a genuine initial four-clique.
The two finite classification/certificate obligations are explicitly exposed
here and discharged by the final theorem in separate modules. -/
theorem twoHomogeneousFours_of_clique_four
    (hclass : SixteenGraphsClassified) (hcores : FixedCoresHaveTwoFours)
    (G : SimpleGraph (Fin 20)) (s : Finset (Fin 20)) (hs : s.card = 4)
    (hclique : G.IsClique (s : Set (Fin 20))) : TwoHomogeneousFours G := by
  classical
  let S : Set (Fin 20) := s
  let H := G.induce (Sᶜ)
  have hcard : Fintype.card ↥(Sᶜ) = 16 := by
    rw [Fintype.card_compl_set]
    simp [S, hs]
  let eFin := H.overFinIso hcard
  by_cases hno : NoHomogeneousFour (H.overFin hcard)
  · rcases hclass (H.overFin hcard) hno with heCore | heCore
    · obtain ⟨a, ⟨e⟩⟩ := exists_fixedCorePattern_iso G _ hs hclique (eFin.trans (Classical.choice heCore))
      exact (hcores.1 a).map_iso e.symm
    · obtain ⟨a, ⟨e⟩⟩ := exists_fixedCorePattern_iso G _ hs hclique (eFin.trans (Classical.choice heCore))
      exact (hcores.2 a).map_iso e.symm
  · have hex : HasCliqueOfSize (H.overFin hcard) 4 ∨
        HasIndependentOfSize (H.overFin hcard) 4 := by
      simpa only [NoHomogeneousFour, not_and_or, not_not] using hno
    rcases hex with hc | hi
    · obtain ⟨t, ht, hth⟩ := hc.map_iso eFin.symm
      exact twoHomogeneousFours_of_induce_compl s hs (Or.inl hclique) t ht (Or.inl hth)
    · obtain ⟨t, ht, hth⟩ := hi.map_iso eFin.symm
      exact twoHomogeneousFours_of_induce_compl s hs (Or.inl hclique) t ht (Or.inr hth)

/-- Ramsey provides a first homogeneous four-set; complementing the whole
ambient graph when needed preserves the conclusion. -/
theorem twenty_twoFours_of_classification
    (hclass : SixteenGraphsClassified) (hcores : FixedCoresHaveTwoFours)
    (G : SimpleGraph (Fin 20)) : TwoHomogeneousFours G := by
  rcases ramsey_four_four G (by simp) with ⟨s, hs, hc⟩ | ⟨s, hs, hi⟩
  · exact twoHomogeneousFours_of_clique_four hclass hcores G s hs hc
  · apply twoHomogeneousFours_compl_iff.mp
    apply twoHomogeneousFours_of_clique_four hclass hcores Gᶜ s hs
    intro u hu v hv huv
    exact ⟨huv, hi hu hv huv⟩

end CochromaticTwenty
#print axioms CochromaticTwenty.twenty_twoFours_of_classification
