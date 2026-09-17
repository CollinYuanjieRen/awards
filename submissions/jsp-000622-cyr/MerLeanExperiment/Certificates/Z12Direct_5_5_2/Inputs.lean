import MerLeanExperiment.Certificates.Z12Direct_5_5_2.Clauses0000_0095

/-! Generated from the actual pinned z12direct_5_5_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through96. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 96 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 96 inputClause
def concreteCNF : CNF Nat := indexedCNF 96 inputClause
/-- Input SHA256: 8232bc8cc4aa17f100e314002f2f7fd5fbe3d748730275e19b86dc099c816a53; LRAT SHA256: 25c4ee95045e8d5a70a80ae55d2924d4b365d31588bf14c475cb464e7ddc901e. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 96 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_2
