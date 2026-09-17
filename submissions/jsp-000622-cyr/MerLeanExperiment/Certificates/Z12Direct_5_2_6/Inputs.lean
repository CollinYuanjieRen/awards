import MerLeanExperiment.Certificates.Z12Direct_5_2_6.Clauses0000_0072

/-! Generated from the actual pinned z12direct_5_2_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through73. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 73 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 73 inputClause
def concreteCNF : CNF Nat := indexedCNF 73 inputClause
/-- Input SHA256: 0601ab2f972f96141186541d570331077d116a45a00499ace9ccb3c74d935cbf; LRAT SHA256: 1beb48e5fe71b50cd960ef73ff6546adbe914e31e85a48afbb58bc4bb5688772. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 73 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_2_6
