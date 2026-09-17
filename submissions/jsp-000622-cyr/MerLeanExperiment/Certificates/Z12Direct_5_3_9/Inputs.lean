import MerLeanExperiment.Certificates.Z12Direct_5_3_9.Clauses0000_0166

/-! Generated from the actual pinned z12direct_5_3_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through167. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 167 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 167 inputClause
def concreteCNF : CNF Nat := indexedCNF 167 inputClause
/-- Input SHA256: 62a02427e9b8bd691d7e682fedf27cac598f9c962671a73c70070af3af9a7aed; LRAT SHA256: 12e4b6a513779752fe4edd84b9fc7b521b762d46f269cd51fb807a7861a8164a. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 167 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_9
