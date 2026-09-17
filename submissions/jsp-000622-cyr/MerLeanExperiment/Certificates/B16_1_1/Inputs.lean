import MerLeanExperiment.Certificates.B16_1_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_1_1.Clauses0250_0333

/-! Generated from the actual pinned b16_1_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through334. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 334 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 334 inputClause
def concreteCNF : CNF Nat := indexedCNF 334 inputClause
/-- Input SHA256: b17f032237afb41a2e8615d904a29c03702e0e30b7d72716359a81cfffe69f2b; LRAT SHA256: a98ac26a06d3b3a410152f6085a0214a976083518b6f7d15c52287f144473a1b. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 334 inputClause a h

end CochromaticTwenty.Certificates.B16_1_1
