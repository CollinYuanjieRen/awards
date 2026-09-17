import MerLeanExperiment.B16Meaning.B16_0_0.All
import MerLeanExperiment.B16Meaning.B16_0_1.All
import MerLeanExperiment.B16Meaning.B16_0_2Enumerating.All
import MerLeanExperiment.B16Meaning.B16_1_0.All
import MerLeanExperiment.B16Meaning.B16_1_1.All
import MerLeanExperiment.B16Meaning.B16_1_2.All
import MerLeanExperiment.B16Meaning.B16_2_0.All
import MerLeanExperiment.B16Meaning.B16_2_1.All
import MerLeanExperiment.B16Meaning.B16_2_2.All
import MerLeanExperiment.B16Meaning.B16_3_0.All
import MerLeanExperiment.B16Meaning.B16_3_1.All
import MerLeanExperiment.B16Meaning.B16_3_2.All
import MerLeanExperiment.B16Meaning.B16_4_0.All
import MerLeanExperiment.B16Meaning.B16_4_1.All
import MerLeanExperiment.B16Meaning.B16_4_2.All
import MerLeanExperiment.B16Meaning.B16_5_0.All
import MerLeanExperiment.B16Meaning.B16_5_1.All
import MerLeanExperiment.B16Meaning.B16_5_2.All
import MerLeanExperiment.B16Meaning.B16_6_0.All
import MerLeanExperiment.B16Meaning.B16_6_1.All
import MerLeanExperiment.B16Meaning.B16_6_2.All
import MerLeanExperiment.B16Meaning.B16_7_0.All
import MerLeanExperiment.B16Meaning.B16_7_1.All
import MerLeanExperiment.B16Meaning.B16_7_2.All
import MerLeanExperiment.B16Meaning.B16_8_0Enumerating.All
import MerLeanExperiment.B16Meaning.B16_8_1.All
import MerLeanExperiment.B16Meaning.B16_8_2.All
import MerLeanExperiment.SmallCatalogData
namespace CochromaticTwenty
set_option maxRecDepth 100000
theorem sixteenCatalogPatterns_classification (left : ℕ) (hl : left ∈ SmallCatalogData.catalog7)
    (right : ℕ) (hr : right ∈ SmallCatalogData.catalog8) (a : ℕ → Bool)
    (hno : NoHomogeneousFour ((neighborhoodPattern 16 7 left right).graph a)) :
    Nonempty ((neighborhoodPattern 16 7 left right).graph a ≃g codeGraph 16 coreCode0) ∨
    Nonempty ((neighborhoodPattern 16 7 left right).graph a ≃g codeGraph 16 coreCode1) := by
  simp only [SmallCatalogData.catalog7, List.mem_cons, List.not_mem_nil, or_false] at hl
  simp only [SmallCatalogData.catalog8, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_0_0.classification a hno
    · exact B16Meaning.B16_0_1.classification a hno
    · exact B16Meaning.B16_0_2Enumerating.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_1_0.classification a hno
    · exact B16Meaning.B16_1_1.classification a hno
    · exact B16Meaning.B16_1_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_2_0.classification a hno
    · exact B16Meaning.B16_2_1.classification a hno
    · exact B16Meaning.B16_2_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_3_0.classification a hno
    · exact B16Meaning.B16_3_1.classification a hno
    · exact B16Meaning.B16_3_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_4_0.classification a hno
    · exact B16Meaning.B16_4_1.classification a hno
    · exact B16Meaning.B16_4_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_5_0.classification a hno
    · exact B16Meaning.B16_5_1.classification a hno
    · exact B16Meaning.B16_5_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_6_0.classification a hno
    · exact B16Meaning.B16_6_1.classification a hno
    · exact B16Meaning.B16_6_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_7_0.classification a hno
    · exact B16Meaning.B16_7_1.classification a hno
    · exact B16Meaning.B16_7_2.classification a hno
  · rcases hr with rfl | rfl | rfl
    · exact B16Meaning.B16_8_0Enumerating.classification a hno
    · exact B16Meaning.B16_8_1.classification a hno
    · exact B16Meaning.B16_8_2.classification a hno
end CochromaticTwenty
#print axioms CochromaticTwenty.sixteenCatalogPatterns_classification
