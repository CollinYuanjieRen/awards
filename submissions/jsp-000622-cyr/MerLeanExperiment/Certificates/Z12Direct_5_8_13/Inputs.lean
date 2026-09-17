import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Clauses0500_0749
import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Clauses0750_0901

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through902. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | 3 => inputBlock3.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 902 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 902 inputClause
def concreteCNF : CNF Nat := indexedCNF 902 inputClause
/-- Input SHA256: fdf20b60eb703c572527a3c16ce5ba99bb925904e0fcce0fee0386e4f3a4c66b; LRAT SHA256: 2511a545c6440fd9111029cc7b00c5eb3ef65f6059318e1a084b9bba3e3d4152. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 902 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
