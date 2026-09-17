import MerLeanExperiment.Certificates.Z12Direct_5_7_5.Clauses0000_0200

/-! Generated from the actual pinned z12direct_5_7_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through201. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 201 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 201 inputClause
def concreteCNF : CNF Nat := indexedCNF 201 inputClause
/-- Input SHA256: 9888f82966b316c55db8ee6e50b3860768a8fc70c9f6862eae4f43bdff735af8; LRAT SHA256: 524ede0c26fd3c5ade6d92ced61ea41dafbbb0e758c9f80cebbe54e8ba805039. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 201 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_5
