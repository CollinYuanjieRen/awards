import MerLeanExperiment.Certificates.B16_2_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_2_1.Clauses0250_0321

/-! Generated from the actual pinned b16_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through322. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 322 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 322 inputClause
def concreteCNF : CNF Nat := indexedCNF 322 inputClause
/-- Input SHA256: c76ce80076632a54d6cae9ad0383ee6407576227702e96c927a992fe34d66f45; LRAT SHA256: 4f0e0f67ea7881aa9a9480790ca355a1585edaf78203891cfe7812b5b3f7d3b9. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 322 inputClause a h

end CochromaticTwenty.Certificates.B16_2_1
