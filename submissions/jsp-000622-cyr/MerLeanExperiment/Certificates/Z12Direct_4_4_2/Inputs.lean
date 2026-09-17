import MerLeanExperiment.Certificates.Z12Direct_4_4_2.Clauses0000_0196

/-! Generated from the actual pinned z12direct_4_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through197. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 197 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 197 inputClause
def concreteCNF : CNF Nat := indexedCNF 197 inputClause
/-- Input SHA256: b204695b100203e43c6a6774eed523b76dfba1b49b73ee3ba5e2e52dc6fb5252; LRAT SHA256: cf1936a3b08ef4fc5e62fe4af95ac6d423ab964be4cdf27b246e6375a1624c76. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 197 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_2
