import MerLeanExperiment.Certificates.B16_3_0.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_3_0.Clauses0250_0370

/-! Generated from the actual pinned b16_3_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through371. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 371 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 371 inputClause
def concreteCNF : CNF Nat := indexedCNF 371 inputClause
/-- Input SHA256: 103c7c2cda7ee290c4f05f3af6bb8a02c61fcad5816bb507a0b67220833c40fd; LRAT SHA256: a77c8e7b2fcc61878132f5577d3c8d5e56b213f4e100febe9aae659bc5b7c84e. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 371 inputClause a h

end CochromaticTwenty.Certificates.B16_3_0
