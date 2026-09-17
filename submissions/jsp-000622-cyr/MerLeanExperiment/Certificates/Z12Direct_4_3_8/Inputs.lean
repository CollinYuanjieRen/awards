import MerLeanExperiment.Certificates.Z12Direct_4_3_8.Clauses0000_0212

/-! Generated from the actual pinned z12direct_4_3_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through213. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 213 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 213 inputClause
def concreteCNF : CNF Nat := indexedCNF 213 inputClause
/-- Input SHA256: c407185b2cbad5c5e8e56517b0616eabfc9b736d11d91122ea001721165e03c8; LRAT SHA256: 7cab9cd5bb6287d002e67119c1cd777727d2278223e3ca0ecfc814f9fbfe3f12. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 213 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_8
