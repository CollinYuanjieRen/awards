import MerLeanExperiment.Certificates.Z12Direct_4_5_1.Clauses0000_0011

/-! Generated from the actual pinned z12direct_4_5_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through12. -/
def inputClause (id : Nat) : DefaultClause 28 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 28 → Bool) : Prop :=
  ∀ i, i < 12 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 28 := indexedFormula 12 inputClause
def concreteCNF : CNF Nat := indexedCNF 12 inputClause
/-- Input SHA256: f8a2b5e5d047635ce807dc20b844f1bdc89a0b11b39baea9d0abbae65cd3d467; LRAT SHA256: bd410a6396c838850a336db7db0eea55e498590f1c44c5b431711aec7ffa7e49. -/
theorem initialFormula_supplies_inputs (a : PosFin 28 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 12 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_1
