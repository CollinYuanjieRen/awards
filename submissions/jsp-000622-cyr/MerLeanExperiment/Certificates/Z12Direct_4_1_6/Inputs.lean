import MerLeanExperiment.Certificates.Z12Direct_4_1_6.Clauses0000_0072

/-! Generated from the actual pinned z12direct_4_1_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through73. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 73 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 73 inputClause
def concreteCNF : CNF Nat := indexedCNF 73 inputClause
/-- Input SHA256: dd6ce0bb94f1fd2e5fd87d051da97ac111170b97ff8e3852df004001e70b58df; LRAT SHA256: 8dbbfa8fec6d3b97131a694f619fbcd244e707dd5fbe2eddf40f27aa315d81a2. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 73 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_6
