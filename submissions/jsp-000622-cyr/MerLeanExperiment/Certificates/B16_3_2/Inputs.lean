import MerLeanExperiment.Certificates.B16_3_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_3_2.Clauses0250_0397

/-! Generated from the actual pinned b16_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through398. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 398 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 398 inputClause
def concreteCNF : CNF Nat := indexedCNF 398 inputClause
/-- Input SHA256: 8a6b108c1177cba352bc4d3eaae8ae05b747fd7719493ea8862d825a899b445c; LRAT SHA256: 9a2130207872a7390034a6a5e8a8d47d8f171f52d3613b164a674d8bd78824e9. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 398 inputClause a h

end CochromaticTwenty.Certificates.B16_3_2
