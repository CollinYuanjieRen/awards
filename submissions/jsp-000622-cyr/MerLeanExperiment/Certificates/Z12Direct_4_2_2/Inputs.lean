import MerLeanExperiment.Certificates.Z12Direct_4_2_2.Clauses0000_0058

/-! Generated from the actual pinned z12direct_4_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through59. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 59 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 59 inputClause
def concreteCNF : CNF Nat := indexedCNF 59 inputClause
/-- Input SHA256: 3ef2dd706b63dc89924564fb3c90f3c4f77afc5addd0b456cabdd563fbcc2476; LRAT SHA256: 7e5b901a9f0b0865ba044362d1a3b6c73ee209b220213ca39b0cb719d9033cb9. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 59 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_2
