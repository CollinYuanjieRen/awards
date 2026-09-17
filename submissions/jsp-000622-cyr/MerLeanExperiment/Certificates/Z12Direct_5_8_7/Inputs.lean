import MerLeanExperiment.Certificates.Z12Direct_5_8_7.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_7.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_7.Clauses0500_0743

/-! Generated from the actual pinned z12direct_5_8_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through744. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 744 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 744 inputClause
def concreteCNF : CNF Nat := indexedCNF 744 inputClause
/-- Input SHA256: beb69eba6090460d09a374cfb2ecd751363b686dc97d8a813e68fa6191491c53; LRAT SHA256: df18c6036471ea0968eb6401741cd78292d1a64bbe0223e5624c455f3e72997b. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 744 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_7
