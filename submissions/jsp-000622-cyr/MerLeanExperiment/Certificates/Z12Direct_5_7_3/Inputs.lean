import MerLeanExperiment.Certificates.Z12Direct_5_7_3.Clauses0000_0071

/-! Generated from the actual pinned z12direct_5_7_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through72. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 72 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 72 inputClause
def concreteCNF : CNF Nat := indexedCNF 72 inputClause
/-- Input SHA256: 370b80e02ef0137a0fb1d3b644dad4edd84692dff6300f8d9ad1a71c29f309de; LRAT SHA256: cdbe677c15abb1cb3bc12a323257c14a018406c566a4048d5b2aa95468196f29. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 72 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_3
