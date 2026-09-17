import MerLeanExperiment.ModelClauses
import MerLeanExperiment.CoreWitnesses
namespace CochromaticTwenty.B16Meaning.B16_8_0Enumerating
def allowedCodes : List ℕ := [567700708560257362446748513803736415, 567051671452941689008906212040545631, 568998663947152044449887723164833119, 568998703556397597727701296104641887, 566889045790591397790568697210639711, 566889006157167327688962496695932255, 567538003650401743994638192120468831, 567538082897907071228413189407151455, 566402357080900056485532173204231519, 568998505510169831338642193138881887, 568998545119415384616455766078690655, 565104560130994668695370545017689439, 562345865257862170860079198865495391, 561696867759790870684324269330830687, 562994941974434022036051519063496031, 562994902365188468758240136557008223, 567700391642771602399310736569177439, 567051354530620225683009918107161951, 566402396690146790354966463555343711, 564455523023678995257528243254498655, 565104401669833937176607954871031135, 564455364557682560460307136409015647, 563806367088614855782512455065572703, 563806406697861589651946745416684895, 564941934468644377477043982354388319, 564941855201796237129434918272406879, 564292897361328704039199490157876575, 564292857708561820823759222847870303, 562346023694849106337816360269944159, 562995060802170681869494428316243295, 561697026196777806162061430735279455, 562995100411416235147305810822731103]
theorem allowedCodes_iso (c : ℕ) (hc : c ∈ allowedCodes) :
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode0) ∨
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode1) := by
  simp only [allowedCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨CoreWitnesses.model_8_0_0_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_1_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_2_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_3_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_4_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_5_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_6_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_7_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_8_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_9_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_10_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_11_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_12_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_13_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_14_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_15_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_16_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_17_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_18_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_19_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_20_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_21_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_22_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_23_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_24_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_25_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_26_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_27_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_28_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_29_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_30_iso⟩
  · exact Or.inr ⟨CoreWitnesses.model_8_0_31_iso⟩
end CochromaticTwenty.B16Meaning.B16_8_0Enumerating
