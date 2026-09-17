import MerLeanExperiment.Certificates.Z12Direct_5_1_2.Clauses0000_0000

/-! Generated from the actual pinned z12direct_5_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through1. -/
def inputClause (id : Nat) : DefaultClause 1 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 1 → Bool) : Prop :=
  ∀ i, i < 1 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 1 := indexedFormula 1 inputClause
def concreteCNF : CNF Nat := indexedCNF 1 inputClause
/-- Input SHA256: 69ee12c3118a428a28f674ec24e362b721e0611c800f65afbcb8a48e778c1394; LRAT SHA256: c691fcc163ea87984efb492e1e16b69e31c4afb07c47284924aabd3371113d7e. -/
theorem initialFormula_supplies_inputs (a : PosFin 1 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 1 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_1_2
