import MerLeanExperiment.Certificates.Z12Direct_5_4_5.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_4_5.Clauses0250_0316

/-! Generated from the actual pinned z12direct_5_4_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through317. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 317 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 317 inputClause
def concreteCNF : CNF Nat := indexedCNF 317 inputClause
/-- Input SHA256: 4f7a1917e71b2c1e5fecc8c9cedef1e12a1e64accca2719902f1c35995715fd0; LRAT SHA256: 161c602b9bc6795c6a170de7b158cd3e4490ad1b9dd51389a7e003aac1056f93. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 317 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_5
