import MerLeanExperiment.Certificates.B16_7_0.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_7_0.Clauses0250_0383

/-! Generated from the actual pinned b16_7_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through384. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 384 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 384 inputClause
def concreteCNF : CNF Nat := indexedCNF 384 inputClause
/-- Input SHA256: 1dcf110ac39377ac62a1d0a2c1d111e1df0fcdf2bfe15f0ea9fd424b75c6637d; LRAT SHA256: fa061224c381cf48a38f1784cd1e90594f85fe893118857934f61c8700a64d12. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 384 inputClause a h

end CochromaticTwenty.Certificates.B16_7_0
