import MerLeanExperiment.Main
import MerLeanExperiment.ModelAdapters
import MerLeanExperiment.Table

#print axioms cochromatic_twenty
#print axioms cochromatic_twelve
#print axioms cochromatic_twelve_on_finite_type
#print axioms CochromaticTwenty.paley17OnTwelve_lowerBound
#print axioms CochromaticTwenty.universal_six_upperBound
#print axioms CochromaticTwenty.paley17_lowerBound
#print axioms CochromaticTwenty.fin8_hasCocoloring_three
#print axioms CochromaticTwenty.fin12_hasCocoloring_four
#print axioms CochromaticTwenty.sixteen_classification
#print axioms CochromaticTwenty.twenty_twoFours
#print axioms CochromaticTwenty.fixedCore0_twoFours
#print axioms CochromaticTwenty.fixedCore1_twoFours
#print axioms CochromaticTwenty.target_iff_on_card_twenty

/-- The checked labelled statement has the same ordinary finite graph meaning
on every twenty-element vertex type. -/
theorem cochromatic_twenty_on_finite_type {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 20) :
    (∀ G : SimpleGraph V, CochromaticTwenty.HasCocoloring G 6) ∧
      (∃ G : SimpleGraph V, ¬ CochromaticTwenty.HasCocoloring G 5) :=
  CochromaticTwenty.target_on_card_twenty cochromatic_twenty hcard

#print axioms cochromatic_twenty_on_finite_type

/-!
The published table `z(1..19)` of maximum cochromatic numbers, its two new
anchors, and the `zmax` characterisation it is stated with.
-/
#print axioms cochromatic_table
#print axioms cochromatic_zmax_table
#print axioms cochromatic_zmax_twenty
#print axioms cochromatic_zmax_twelve
#print axioms CochromaticTwenty.fin15_hasCocoloring_five
#print axioms CochromaticTwenty.fin9_not_hasCocoloring_three
#print axioms CochromaticTwenty.zmax_eq_iff
