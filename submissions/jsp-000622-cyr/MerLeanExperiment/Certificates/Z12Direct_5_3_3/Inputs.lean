import MerLeanExperiment.Certificates.Z12Direct_5_3_3.Clauses0000_0125

/-! Generated from the actual pinned z12direct_5_3_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through126. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 126 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 126 inputClause
def concreteCNF : CNF Nat := indexedCNF 126 inputClause
/-- Input SHA256: 0f5b932372d6405ce3f33a01826e3b209c387a50e1feee686ed8614b8e9bd2a3; LRAT SHA256: 13b9332be5e0148956ec1bc5a48c9dd7a3a24fefe2ed34cfc1e128bb3bfcf855. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 126 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_3
