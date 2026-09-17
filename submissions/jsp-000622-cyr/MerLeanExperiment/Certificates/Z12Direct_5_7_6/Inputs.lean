import MerLeanExperiment.Certificates.Z12Direct_5_7_6.Clauses0000_0083

/-! Generated from the actual pinned z12direct_5_7_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through84. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 84 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 84 inputClause
def concreteCNF : CNF Nat := indexedCNF 84 inputClause
/-- Input SHA256: 593b442c950a0813bd1ef0ce2897d32f7a2ce108b28a077f79a052d7f3656a1e; LRAT SHA256: 7c433d859f9227c2125a5a45407cf928ed00b3996c6cd4b5ca73f88bbad54048. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 84 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_6
