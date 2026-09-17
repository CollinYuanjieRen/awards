import MerLeanExperiment.Certificates.B16_6_0.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_6_0.Clauses0250_0395

/-! Generated from the actual pinned b16_6_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through396. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 396 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 396 inputClause
def concreteCNF : CNF Nat := indexedCNF 396 inputClause
/-- Input SHA256: 51c446560cabbfd540bd69f1981163ed11f45bd463b0009a8868b9b7fde0efd1; LRAT SHA256: 78a019d3969ed3d19aa8a05e1732b896d05f49951ddce36b4d0a9c52073a0716. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 396 inputClause a h

end CochromaticTwenty.Certificates.B16_6_0
