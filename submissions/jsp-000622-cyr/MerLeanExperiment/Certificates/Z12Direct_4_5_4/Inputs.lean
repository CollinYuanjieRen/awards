import MerLeanExperiment.Certificates.Z12Direct_4_5_4.Clauses0000_0081

/-! Generated from the actual pinned z12direct_4_5_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through82. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 82 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 82 inputClause
def concreteCNF : CNF Nat := indexedCNF 82 inputClause
/-- Input SHA256: 0e3257f34c66cb09fc924326da7612068cc35492134d355e89518f3b31925db0; LRAT SHA256: ad59d84264baff2331d16457adcaba007c2b7e2304252c0b905699bd44d33b54. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 82 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_4
