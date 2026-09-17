import MerLeanExperiment.Certificates.Z12Direct_4_0_3.Clauses0000_0045

/-! Generated from the actual pinned z12direct_4_0_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through46. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 46 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 46 inputClause
def concreteCNF : CNF Nat := indexedCNF 46 inputClause
/-- Input SHA256: 6d85efebe33180725ff6c5c0f586b9fe62d086d071931e09dff289e640a3072a; LRAT SHA256: d2115b843890e5eb693ffefec41c173adc17f8446609a52d95cf29f26e16b1c7. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 46 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_3
