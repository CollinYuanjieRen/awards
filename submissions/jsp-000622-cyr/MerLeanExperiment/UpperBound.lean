import MerLeanExperiment.TwentyTwoFours
import MerLeanExperiment.TwelveColoring

namespace CochromaticTwenty

theorem universal_six_upperBound : UpperBound := by
  intro G
  obtain ⟨s, t, hs, ht, hd, hsh, hth⟩ := twenty_twoFours G
  exact hasCocoloring_six_of_two_disjoint_homogeneous_four (by simp)
    fin12_hasCocoloring_four hd hs ht hsh hth

end CochromaticTwenty
#print axioms CochromaticTwenty.universal_six_upperBound
