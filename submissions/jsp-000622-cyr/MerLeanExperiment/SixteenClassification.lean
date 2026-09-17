import MerLeanExperiment.SixteenClassificationReduction
import MerLeanExperiment.SixteenCatalogClassification

namespace CochromaticTwenty

theorem sixteen_classification (G : SimpleGraph (Fin 16)) (hG : NoHomogeneousFour G) :
    Nonempty (G ≃g codeGraph 16 coreCode0) ∨
      Nonempty (G ≃g codeGraph 16 coreCode1) :=
  sixteen_classification_of_catalog_patterns sixteenCatalogPatterns_classification G hG

end CochromaticTwenty
#print axioms CochromaticTwenty.sixteen_classification
