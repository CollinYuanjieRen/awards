import MerLeanExperiment.Certificates.B16_5_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_5_2.Clauses0250_0351

/-! Generated from the actual pinned b16_5_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_5_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through352. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 352 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 352 inputClause
def concreteCNF : CNF Nat := indexedCNF 352 inputClause
/-- Input SHA256: d6b60a873e5adba54d8686f0b12ea7bfca74222526844c7b4ee8334139924692; LRAT SHA256: 51df535751c6d31fbde87483dc948762f319e4723b81ab7065ca16d811fab36a. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 352 inputClause a h

end CochromaticTwenty.Certificates.B16_5_2
