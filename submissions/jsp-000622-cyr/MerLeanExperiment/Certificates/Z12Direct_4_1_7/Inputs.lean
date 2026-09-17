import MerLeanExperiment.Certificates.Z12Direct_4_1_7.Clauses0000_0107

/-! Generated from the actual pinned z12direct_4_1_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through108. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 108 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 108 inputClause
def concreteCNF : CNF Nat := indexedCNF 108 inputClause
/-- Input SHA256: c013e9ae508615fde5551f5efab5f22350224251043adead23ed3dd5b7e00d68; LRAT SHA256: 07382e0f9333eb3941a1bd0d9db89c2c9804599e8f686d013b6879d77440005e. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 108 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_7
