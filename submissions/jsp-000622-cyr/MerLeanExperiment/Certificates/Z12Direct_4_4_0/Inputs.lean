import MerLeanExperiment.Certificates.Z12Direct_4_4_0.Clauses0000_0125

/-! Generated from the actual pinned z12direct_4_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through126. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 126 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 126 inputClause
def concreteCNF : CNF Nat := indexedCNF 126 inputClause
/-- Input SHA256: f227c8c443ff34139bbfaf9ab8d16ecd4d192fb59beda0e39421154a890cef58; LRAT SHA256: 19903bce393c5051cff26ce136a011fbd988102d179672102353ed3e86574cac. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 126 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_0
