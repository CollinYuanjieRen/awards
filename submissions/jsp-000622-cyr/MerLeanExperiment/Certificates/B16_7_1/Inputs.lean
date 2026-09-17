import MerLeanExperiment.Certificates.B16_7_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_7_1.Clauses0250_0356

/-! Generated from the actual pinned b16_7_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through357. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 357 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 357 inputClause
def concreteCNF : CNF Nat := indexedCNF 357 inputClause
/-- Input SHA256: c40586e5997fc0e753b760299b6325be65ef49a2b9e7274691ef6754a0907e55; LRAT SHA256: 5c49172fb0fe5c08961994181368e01625f1d158b88eb878d87ae61a784c2044. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 357 inputClause a h

end CochromaticTwenty.Certificates.B16_7_1
