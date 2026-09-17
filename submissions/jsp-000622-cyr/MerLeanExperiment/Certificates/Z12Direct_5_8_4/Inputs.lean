import MerLeanExperiment.Certificates.Z12Direct_5_8_4.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_4.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_4.Clauses0500_0529

/-! Generated from the actual pinned z12direct_5_8_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_4
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
/-- Input SHA256: 1d5c0603a698dbc7b15a63abc5fbba1b4f9ae2c999306ad94f1c90402c60472f; LRAT SHA256: 0e3b51e4c9beb3a603abd887ab283dd30a700e58303bfbaeb2e2a600d515f09f. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 530 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_4
