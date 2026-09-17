import MerLeanExperiment.Certificates.Z12Direct_5_6_7.Clauses0000_0184

/-! Generated from the actual pinned z12direct_5_6_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through185. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 185 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 185 inputClause
def concreteCNF : CNF Nat := indexedCNF 185 inputClause
/-- Input SHA256: 49a62a92a7ec42d0b75a4c6fcf0bf0405d70af7708e15ba6739e2c54e611ed49; LRAT SHA256: 4f42f6043dc772384d4022aa147e9c9732b141664f4c1703bf0d05cc6ef86e84. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 185 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_7
