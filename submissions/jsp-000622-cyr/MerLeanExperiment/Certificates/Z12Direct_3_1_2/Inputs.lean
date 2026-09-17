import MerLeanExperiment.Certificates.Z12Direct_3_1_2.Clauses0000_0011

/-! Generated from the actual pinned z12direct_3_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through12. -/
def inputClause (id : Nat) : DefaultClause 9 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 9 → Bool) : Prop :=
  ∀ i, i < 12 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 9 := indexedFormula 12 inputClause
def concreteCNF : CNF Nat := indexedCNF 12 inputClause
/-- Input SHA256: 110bf5faa88169b805669042a890892a9f4926d6fa886aaa41a6fd3141898b27; LRAT SHA256: 90a2d53a31c59adb51875d07abe9d104e62236b03434026988ad08562a111520. -/
theorem initialFormula_supplies_inputs (a : PosFin 9 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 12 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_1_2
