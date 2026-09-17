import MerLeanExperiment.Certificates.B16_8_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_8_2.Clauses0250_0379

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through380. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 380 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 380 inputClause
def concreteCNF : CNF Nat := indexedCNF 380 inputClause
/-- Input SHA256: 77d4cae6f54ae74c48646d467111f5e20726a2a21b1147e82d31be00c728f164; LRAT SHA256: 64aaeb8295da8dcad6ab90e7a7aab671d96b388ced623ecb5c3a8d074f91a238. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 380 inputClause a h

end CochromaticTwenty.Certificates.B16_8_2
