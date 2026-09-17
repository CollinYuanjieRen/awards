import MerLeanExperiment.Certificates.Z12Direct_5_6_11.Clauses0000_0109

/-! Generated from the actual pinned z12direct_5_6_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through110. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 110 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 110 inputClause
def concreteCNF : CNF Nat := indexedCNF 110 inputClause
/-- Input SHA256: b10929e9815f10713cff5b378f2e75583d6aa78d606e2051e1167344a1e1fd97; LRAT SHA256: 8d023d4aa8df4ba99a2b9b77711e95436f06fded373b0f38092749ef2ef559a8. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 110 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_11
