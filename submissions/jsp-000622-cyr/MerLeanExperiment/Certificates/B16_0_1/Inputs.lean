import MerLeanExperiment.Certificates.B16_0_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_0_1.Clauses0250_0325

/-! Generated from the actual pinned b16_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through326. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 326 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 326 inputClause
def concreteCNF : CNF Nat := indexedCNF 326 inputClause
/-- Input SHA256: edc6b42b4c07b7d3dfdacb42caa38914a6536707e24990ade5ab7161cc4e1dfb; LRAT SHA256: 7a0a1a3eced0b94d860ada9d0039e25d38d627b4750347a35c81578b3a09fdc4. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 326 inputClause a h

end CochromaticTwenty.Certificates.B16_0_1
