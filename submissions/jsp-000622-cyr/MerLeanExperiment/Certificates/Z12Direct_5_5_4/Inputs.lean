import MerLeanExperiment.Certificates.Z12Direct_5_5_4.Clauses0000_0147

/-! Generated from the actual pinned z12direct_5_5_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through148. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 148 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 148 inputClause
def concreteCNF : CNF Nat := indexedCNF 148 inputClause
/-- Input SHA256: c320efd48a3e290fed8ad88e06001d7e74e8a18d9fe933feafaeb83357818d6f; LRAT SHA256: bf9bf594fe28958d66fd0f1bc76600e82760a25c4f6f4240adfca2e98ab96a09. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 148 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_4
