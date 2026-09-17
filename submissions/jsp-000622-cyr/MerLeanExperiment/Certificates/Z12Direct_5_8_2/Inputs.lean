import MerLeanExperiment.Certificates.Z12Direct_5_8_2.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_2.Clauses0250_0294

/-! Generated from the actual pinned z12direct_5_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through295. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 295 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 295 inputClause
def concreteCNF : CNF Nat := indexedCNF 295 inputClause
/-- Input SHA256: cd161fe6277c0781d9e51d64656af873eb0f8e3fe508e1cc5098eacda0a7e1be; LRAT SHA256: f4a8b4bd56eb33406a1f1206de9d4f124baff0ac1c87c882b3de76e142dbb7c1. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 295 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_2
