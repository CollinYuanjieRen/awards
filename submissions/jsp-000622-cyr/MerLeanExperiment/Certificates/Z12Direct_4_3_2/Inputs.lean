import MerLeanExperiment.Certificates.Z12Direct_4_3_2.Clauses0000_0072

/-! Generated from the actual pinned z12direct_4_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through73. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 73 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 73 inputClause
def concreteCNF : CNF Nat := indexedCNF 73 inputClause
/-- Input SHA256: a518be3c7b447c8fcdf56a813ad50e2c768b20a7bacbca64bd0d4816c9a6bcbc; LRAT SHA256: 4ee04c989097bc250b35f49dfe0f4181f3d68d7dc87861d9e2be80a4de3063ed. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 73 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_2
