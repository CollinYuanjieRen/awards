import MerLeanExperiment.Certificates.Z12Direct_5_5_11.Clauses0000_0246

/-! Generated from the actual pinned z12direct_5_5_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through247. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 247 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 247 inputClause
def concreteCNF : CNF Nat := indexedCNF 247 inputClause
/-- Input SHA256: 20889d31135dc3bde371a341fef06d9632f92a4e0a2f3fc539c50bc407fc1028; LRAT SHA256: 03626d48a6b045758c000153cbf4e3628346ac49a6c37be234742d023ddfbb2a. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 247 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_11
