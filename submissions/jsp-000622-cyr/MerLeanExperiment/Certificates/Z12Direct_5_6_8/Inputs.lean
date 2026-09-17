import MerLeanExperiment.Certificates.Z12Direct_5_6_8.Clauses0000_0141

/-! Generated from the actual pinned z12direct_5_6_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through142. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 142 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 142 inputClause
def concreteCNF : CNF Nat := indexedCNF 142 inputClause
/-- Input SHA256: e98d6bba33884f7dc6498324dfee58059173e21442d55484b9cb0ac2a7b0d42c; LRAT SHA256: ea1f90b093c19bce14fd459a4e28e40c47bf9e7a782db84eafd05951d00850ef. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 142 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_8
