import MerLeanExperiment.Certificates.Z12Direct_4_3_1.Clauses0000_0069

/-! Generated from the actual pinned z12direct_4_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through70. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 70 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 70 inputClause
def concreteCNF : CNF Nat := indexedCNF 70 inputClause
/-- Input SHA256: 7079fe350dfcbd7aa0f0c0501bc1cf99188b4962ca97a9f66a248d0e3beabf8d; LRAT SHA256: 49410ea692639064f3bff7ae0d8d2e334cd858ee86c331363b266b554fe1fc59. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 70 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_1
