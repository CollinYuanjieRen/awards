import MerLeanExperiment.ModelClauses
import MerLeanExperiment.CoreWitnesses
namespace CochromaticTwenty.B16Meaning.B16_4_0
def allowedCodes : List ℕ := []
theorem allowedCodes_iso (c : ℕ) (hc : c ∈ allowedCodes) :
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode0) ∨
    Nonempty (codeGraph 16 c ≃g codeGraph 16 coreCode1) := by
  simp [allowedCodes] at hc
end CochromaticTwenty.B16Meaning.B16_4_0
