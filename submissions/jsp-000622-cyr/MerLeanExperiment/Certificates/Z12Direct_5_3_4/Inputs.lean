import MerLeanExperiment.Certificates.Z12Direct_5_3_4.Clauses0000_0209

/-! Generated from the actual pinned z12direct_5_3_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through210. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 210 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 210 inputClause
def concreteCNF : CNF Nat := indexedCNF 210 inputClause
/-- Input SHA256: f543fc6a7fde8ca6cdcb7286b9b8ff6d7644496788f57df1ee252d3711ddd40b; LRAT SHA256: 86b80202df72cfc16f22983ec3fc854c8b5e0a72239ce6aa6fff3f86c23a8ae9. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 210 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_4
