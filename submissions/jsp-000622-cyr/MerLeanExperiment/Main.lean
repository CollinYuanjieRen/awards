import MerLeanExperiment.UpperBound
import MerLeanExperiment.LowerBound
import MerLeanExperiment.Twelve

/-- The maximum cochromatic number of an ordinary twenty-vertex graph is six. -/
theorem cochromatic_twenty : CochromaticTwenty.Target :=
  ⟨CochromaticTwenty.universal_six_upperBound, CochromaticTwenty.paley17_lowerBound⟩

#print axioms cochromatic_twenty

/-- The maximum cochromatic number of an ordinary twelve-vertex graph is four
(`z(12) = 4`); re-exported here so that the root module states both values. -/
theorem cochromatic_twelve' : CochromaticTwenty.TargetTwelve :=
  cochromatic_twelve

#print axioms cochromatic_twelve'
