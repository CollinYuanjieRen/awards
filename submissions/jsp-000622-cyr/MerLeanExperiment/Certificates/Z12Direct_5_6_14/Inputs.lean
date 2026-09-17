import MerLeanExperiment.Certificates.Z12Direct_5_6_14.Clauses0000_0065

/-! Generated from the actual pinned z12direct_5_6_14-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through66. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 66 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 66 inputClause
def concreteCNF : CNF Nat := indexedCNF 66 inputClause
/-- Input SHA256: 908a43e0d1ec96a091fef47ba71f5955e7472f99cd532bf5e2eeac887e77476b; LRAT SHA256: a510a28c548bc002372326e571483948add4e976f28e17c404006aa660e9c261. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 66 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_14
