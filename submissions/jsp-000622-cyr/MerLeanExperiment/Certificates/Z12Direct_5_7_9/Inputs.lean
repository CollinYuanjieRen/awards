import MerLeanExperiment.Certificates.Z12Direct_5_7_9.Clauses0000_0117

/-! Generated from the actual pinned z12direct_5_7_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through118. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 118 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 118 inputClause
def concreteCNF : CNF Nat := indexedCNF 118 inputClause
/-- Input SHA256: dc9c7d225b20322791124b06f3a6a483722fbb5fdfd7b9c4c3216520a1adb1f3; LRAT SHA256: 5bc872371e30e1b91f77b4783dc4b238f5da1c2da46dc9b010fa006610420bac. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 118 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_9
