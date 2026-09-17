import MerLeanExperiment.Certificates.Z12Direct_5_7_0.Clauses0000_0101

/-! Generated from the actual pinned z12direct_5_7_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through102. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 102 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 102 inputClause
def concreteCNF : CNF Nat := indexedCNF 102 inputClause
/-- Input SHA256: 9fa6ec855635faf3a77fba3ee394b7819ae722605266793900a37674ba3d5a11; LRAT SHA256: 7ec83cb68ad0df04742fd42363d61b4d4d2bce1ca0ad5e753690f50fea61569c. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 102 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_0
