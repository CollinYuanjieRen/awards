import MerLeanExperiment.Certificates.Z12Direct_5_3_8.Clauses0000_0216

/-! Generated from the actual pinned z12direct_5_3_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through217. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 217 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 217 inputClause
def concreteCNF : CNF Nat := indexedCNF 217 inputClause
/-- Input SHA256: 98bf132401ebee70edf9e40dd96bf7df0eee5ab8bccde0259321980b1c5b32f2; LRAT SHA256: dccd138f0d1a35e92abef00a07fdb7fc319976346e2de93dc07d0fae46b117fb. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 217 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_8
