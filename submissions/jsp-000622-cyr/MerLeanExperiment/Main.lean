import MerLeanExperiment.UpperBound
import MerLeanExperiment.LowerBound

/-- The maximum cochromatic number of an ordinary twenty-vertex graph is six. -/
theorem cochromatic_twenty : CochromaticTwenty.Target :=
  ⟨CochromaticTwenty.universal_six_upperBound, CochromaticTwenty.paley17_lowerBound⟩

#print axioms cochromatic_twenty
