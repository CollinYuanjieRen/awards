import MerLeanExperiment.Certificates.Z12Direct_4_0_7.Clauses0000_0143

/-! Generated from the actual pinned z12direct_4_0_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through144. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 144 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 144 inputClause
def concreteCNF : CNF Nat := indexedCNF 144 inputClause
/-- Input SHA256: 6ff27bab2055e271224407f5a86ef0383ab5fefdf80384ff10c0c47dff85f874; LRAT SHA256: 0b35e2dee7c89fec1032c60c94439b2c40b319d2747750ba07bb9f4e7ee70735. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 144 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_7
