import MerLeanExperiment.Certificates.Z12Direct_4_2_6.Clauses0000_0021

/-! Generated from the actual pinned z12direct_4_2_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through22. -/
def inputClause (id : Nat) : DefaultClause 22 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 22 → Bool) : Prop :=
  ∀ i, i < 22 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 22 := indexedFormula 22 inputClause
def concreteCNF : CNF Nat := indexedCNF 22 inputClause
/-- Input SHA256: cb8de927c7f47c28004219b9bd59dd6424459e1ac38f0f8cdd2c82134daa0aa6; LRAT SHA256: e65b2e62d9a81bac5c930377e33d25246651a07b807d5752ee0cd4fe857e410b. -/
theorem initialFormula_supplies_inputs (a : PosFin 22 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 22 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_6
