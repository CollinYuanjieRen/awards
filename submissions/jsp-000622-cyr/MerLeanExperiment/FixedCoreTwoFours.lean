import MerLeanExperiment.FixedCore0Meaning.All
import MerLeanExperiment.FixedCore1Meaning.All
import MerLeanExperiment.Certificates.FixedCore0.Complete
import MerLeanExperiment.Certificates.FixedCore1.Complete

namespace CochromaticTwenty

theorem fixedCore0_twoFours (a : ℕ → Bool) :
    TwoHomogeneousFours ((fixedCorePattern coreCode0).graph a) :=
  twoHomogeneousFours_of_unsat (fixedCorePattern coreCode0)
    Certificates.FixedCore0.concreteCNF Certificates.FixedCore0.concreteCNF_unsat
    FixedCore0Meaning.all_inputs_explained a

theorem fixedCore1_twoFours (a : ℕ → Bool) :
    TwoHomogeneousFours ((fixedCorePattern coreCode1).graph a) :=
  twoHomogeneousFours_of_unsat (fixedCorePattern coreCode1)
    Certificates.FixedCore1.concreteCNF Certificates.FixedCore1.concreteCNF_unsat
    FixedCore1Meaning.all_inputs_explained a

end CochromaticTwenty
#print axioms CochromaticTwenty.fixedCore0_twoFours
#print axioms CochromaticTwenty.fixedCore1_twoFours
