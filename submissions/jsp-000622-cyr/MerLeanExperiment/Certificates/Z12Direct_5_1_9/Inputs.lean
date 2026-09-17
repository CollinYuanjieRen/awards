import MerLeanExperiment.Certificates.Z12Direct_5_1_9.Clauses0000_0089

/-! Generated from the actual pinned z12direct_5_1_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through90. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 90 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 90 inputClause
def concreteCNF : CNF Nat := indexedCNF 90 inputClause
/-- Input SHA256: 901da26c78f6656bbea2fcb79088898e0d771436a3a9ea0b3ce99cbeef43bd2a; LRAT SHA256: 902535924f85d2f23d2f3b8b5a9e9b422eeb35a58e52348affa025e1471a871d. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 90 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_1_9
