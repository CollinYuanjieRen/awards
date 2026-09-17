import MerLeanExperiment.TwentyReduction
import MerLeanExperiment.SixteenClassification
import MerLeanExperiment.FixedCoreTwoFours

namespace CochromaticTwenty

theorem twenty_twoFours (G : SimpleGraph (Fin 20)) : TwoHomogeneousFours G :=
  twenty_twoFours_of_classification sixteen_classification
    ⟨fixedCore0_twoFours, fixedCore1_twoFours⟩ G

end CochromaticTwenty
#print axioms CochromaticTwenty.twenty_twoFours
