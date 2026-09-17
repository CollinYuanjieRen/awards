import MerLeanExperiment.Certificates.Z12Direct_5_8_11.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_11.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_11.Clauses0500_0510

/-! Generated from the actual pinned z12direct_5_8_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through511. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 511 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 511 inputClause
def concreteCNF : CNF Nat := indexedCNF 511 inputClause
/-- Input SHA256: 1dfd0b108fe57012e2ecec9731d858c03deedd22e3a48a19daa85d6c05b3479c; LRAT SHA256: bee9e5cd0bd92e28241b59f9af684008d6770389db70a3ded4859f6c3c454700. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 511 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_11
