import MerLeanExperiment.Certificates.Z12Direct_5_3_6.Clauses0000_0202

/-! Generated from the actual pinned z12direct_5_3_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through203. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 203 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 203 inputClause
def concreteCNF : CNF Nat := indexedCNF 203 inputClause
/-- Input SHA256: e4dd031831c5c967961c769dd227b3fbab20bab7350393a54e368ee3430b95d0; LRAT SHA256: f428452e347e4cd565638acb3330a09c9738f1948dbe114910a92ed401d922e3. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 203 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_6
