import MerLeanExperiment.Certificates.Z12Direct_5_5_9.Clauses0000_0121

/-! Generated from the actual pinned z12direct_5_5_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through122. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 122 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 122 inputClause
def concreteCNF : CNF Nat := indexedCNF 122 inputClause
/-- Input SHA256: a2c0f949c3d03759ad1b65276391721fb41762dd557745fbb26e3a41781a31d8; LRAT SHA256: 4a8c718c2cc0f2f645ff8ddb5ae27482baeafe93d76ec8117de4c67aaef70c0b. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 122 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_9
