import MerLeanExperiment.Certificates.Z12Direct_5_8_14.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_14.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_14.Clauses0500_0529

/-! Generated from the actual pinned z12direct_5_8_14-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through530. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 530 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 530 inputClause
def concreteCNF : CNF Nat := indexedCNF 530 inputClause
/-- Input SHA256: ccd4e6467633df1bb995dc4c6ce6ff5559ba9732626f1d0a1b6cd41282c9c34a; LRAT SHA256: 6edd2f5a200302992158fadcca9f4d45de3e1201a783ef5f5288963df137da12. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 530 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_14
