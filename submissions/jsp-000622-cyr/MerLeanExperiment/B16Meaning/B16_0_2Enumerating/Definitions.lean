import MerLeanExperiment.ModelClauses
import MerLeanExperiment.CoreWitnesses
namespace CochromaticTwenty.B16Meaning.B16_0_2Enumerating
def allowedCodes : List ℕ := [1033524294936737235384115735117026507, 1037337368125511127389810778040554699, 1034173312217670504124281626490688715, 1036607032989721505740760291957134539, 1029873065057004482010659550448178379, 1029873238384314364969178735834420427, 1034254065507212810847059763749311691, 1030197524207665615481363609463149771, 1032307285995497805902074060054320331, 1037337041278518752721264093330527435, 1036282554049535155408359906119898315, 1032955976437298635325823292674528459, 1029142903248524743320128249751000267, 1034254238866567045625801362650813643, 1035552273429042759373819498177352907, 1032226205866823059862879264042243275, 1036282747166370255228575418328405195, 1036363564846315174242707790162678987, 1030197717324500715301579121671656651, 1032956243856527554884882754501465291, 1035552080320067594905734011925419211, 1032306959156365366585657401300866251, 1029143230095517117988674934461027531, 1030116439140536128728394189317199051, 1030928191053968275804205015866135755, 1036607206317031388699279477343376587, 1036363832233499741981544838474355915, 1030927997944993111336119529614202059, 1033524027517508315825056273290089675, 1030116706527720696467231237628875979, 1032226032507468825084137665140741323, 1034172985378538064807864967737234635]
theorem allowedCodes_iso (c : ℕ) (hc : c ∈ allowedCodes) :
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode0) ∨
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode1) := by
  simp only [allowedCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨CoreWitnesses.model_0_2_0_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_1_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_2_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_3_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_4_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_5_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_6_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_7_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_8_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_9_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_10_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_11_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_12_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_13_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_14_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_15_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_16_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_17_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_18_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_19_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_20_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_21_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_22_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_23_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_24_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_25_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_26_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_27_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_28_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_29_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_30_iso⟩
  · exact Or.inl ⟨CoreWitnesses.model_0_2_31_iso⟩
end CochromaticTwenty.B16Meaning.B16_0_2Enumerating
