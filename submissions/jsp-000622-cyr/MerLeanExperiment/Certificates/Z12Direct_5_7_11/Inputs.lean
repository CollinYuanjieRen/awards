import MerLeanExperiment.Certificates.Z12Direct_5_7_11.Clauses0000_0173

/-! Generated from the actual pinned z12direct_5_7_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through174. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 174 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 174 inputClause
def concreteCNF : CNF Nat := indexedCNF 174 inputClause
/-- Input SHA256: 9bd07737914f298af6aef80d52677772866e254c8ba3d8a3c4b3a5f2db96dda9; LRAT SHA256: 64a9cfe2c28883e204ec38cd3628fc8e67b63d0587d34373605b2f92420b0058. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 174 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_11
