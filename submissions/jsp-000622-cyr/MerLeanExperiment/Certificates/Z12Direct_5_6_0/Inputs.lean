import MerLeanExperiment.Certificates.Z12Direct_5_6_0.Clauses0000_0078

/-! Generated from the actual pinned z12direct_5_6_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through79. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 79 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 79 inputClause
def concreteCNF : CNF Nat := indexedCNF 79 inputClause
/-- Input SHA256: e52031288b7f0359fec5484d850ee74edab113f921dd5beea6fbcf234d1896fc; LRAT SHA256: e48074fd6284de6ae7c6a0749812353a1ca45f2a451c48fd25cdb2ff200c47a3. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 79 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_0
