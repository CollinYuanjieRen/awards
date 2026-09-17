import MerLeanExperiment.Certificates.Z12Direct_3_2_2.Clauses0000_0011

/-! Generated from the actual pinned z12direct_3_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through12. -/
def inputClause (id : Nat) : DefaultClause 17 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 17 → Bool) : Prop :=
  ∀ i, i < 12 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 17 := indexedFormula 12 inputClause
def concreteCNF : CNF Nat := indexedCNF 12 inputClause
/-- Input SHA256: 79323ace0322a392a1f146c6ea570b324c37f23f5687c0371df9b99b8ab935ab; LRAT SHA256: 8434d8de8c6a2f04ac9e1ea390102f8a834d778ac2b82d9b5185b92959783332. -/
theorem initialFormula_supplies_inputs (a : PosFin 17 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 12 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_2_2
