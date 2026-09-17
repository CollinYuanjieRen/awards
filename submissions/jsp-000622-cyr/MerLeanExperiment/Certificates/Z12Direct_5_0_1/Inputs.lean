import MerLeanExperiment.Certificates.Z12Direct_5_0_1.Clauses0000_0151

/-! Generated from the actual pinned z12direct_5_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through152. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 152 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 152 inputClause
def concreteCNF : CNF Nat := indexedCNF 152 inputClause
/-- Input SHA256: 029be8dece455fcab9c68aff30f6b42b3359c73f8e4bb44a57447bd6144124e0; LRAT SHA256: dbf4237db9de8d438d188fd7b638eeff639420187ad34aebb931438e021fe5df. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 152 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_1
