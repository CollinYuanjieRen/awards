import MerLeanExperiment.Certificates.Z12Direct_5_5_12.Clauses0000_0210

/-! Generated from the actual pinned z12direct_5_5_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through211. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 211 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 211 inputClause
def concreteCNF : CNF Nat := indexedCNF 211 inputClause
/-- Input SHA256: 5921b60bf1d3c0e8776fe5d01ffca7ef75e2913eadab672b8d187e7d4ac8e4eb; LRAT SHA256: 870c57c1a5f7f69a0e09cdb3ef7df9b325470816504da9fa04e52c7677631af4. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 211 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_12
