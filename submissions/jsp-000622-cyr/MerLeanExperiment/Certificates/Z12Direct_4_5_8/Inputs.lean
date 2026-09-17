import MerLeanExperiment.Certificates.Z12Direct_4_5_8.Clauses0000_0107

/-! Generated from the actual pinned z12direct_4_5_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through108. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 108 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 108 inputClause
def concreteCNF : CNF Nat := indexedCNF 108 inputClause
/-- Input SHA256: 357cbb4e0916b2f42d9bae4afe72d7b056b0d9eb1daadbfa8333d9453ec7c149; LRAT SHA256: 5e0250d38dbeac76b76a52a264d3a7c82660edb8d020f7d655391ea39e4e685c. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 108 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_8
