import MerLeanExperiment.Certificates.Z12Direct_4_0_2.Clauses0000_0149

/-! Generated from the actual pinned z12direct_4_0_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through150. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 150 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 150 inputClause
def concreteCNF : CNF Nat := indexedCNF 150 inputClause
/-- Input SHA256: ed5e905595ddb5e87cea1eb73ab0674257468d77ba80208f43977a57a27282b4; LRAT SHA256: c0f80aae799964d136f44b5138f007267444af074d12638b31c0d724cb422881. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 150 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_2
