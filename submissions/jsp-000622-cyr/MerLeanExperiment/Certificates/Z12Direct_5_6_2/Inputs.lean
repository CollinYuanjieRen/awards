import MerLeanExperiment.Certificates.Z12Direct_5_6_2.Clauses0000_0074

/-! Generated from the actual pinned z12direct_5_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through75. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 75 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 75 inputClause
def concreteCNF : CNF Nat := indexedCNF 75 inputClause
/-- Input SHA256: 55a5fea8609755e52189b638b70c3846e2bc80a5939eed076e8c2745db201397; LRAT SHA256: 04c144178d8a0f8d6cfb31e62f28d96d4b59167cf390a3890adeddc84c63cda5. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 75 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_2
