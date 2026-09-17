import MerLeanExperiment.Certificates.Z12Direct_4_0_1.Clauses0000_0010

/-! Generated from the actual pinned z12direct_4_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through11. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 11 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 11 inputClause
def concreteCNF : CNF Nat := indexedCNF 11 inputClause
/-- Input SHA256: c09080f702d0c988c5b6981719096df785bbdfa7820c7858adc2a848786c60c0; LRAT SHA256: bddbf9ef5354a5f02741d6c45cc89776b407a36792bbf0ad33a910a8ebd3a707. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 11 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_1
