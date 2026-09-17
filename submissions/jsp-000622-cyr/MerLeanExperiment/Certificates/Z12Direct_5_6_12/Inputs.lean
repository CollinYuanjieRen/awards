import MerLeanExperiment.Certificates.Z12Direct_5_6_12.Clauses0000_0115

/-! Generated from the actual pinned z12direct_5_6_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through116. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 116 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 116 inputClause
def concreteCNF : CNF Nat := indexedCNF 116 inputClause
/-- Input SHA256: a2bc57149b2ca14a304a2bd677ff2b6131ddfa844ceb00105eb3002269d5eee0; LRAT SHA256: e498b4d0a8b998c7d24743b7a6b2de4f0cc25d3edf212d4fc4895f47261a2cb4. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 116 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_12
