import MerLeanExperiment.Certificates.Z12Direct_5_3_0.Clauses0000_0196

/-! Generated from the actual pinned z12direct_5_3_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through197. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 197 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 197 inputClause
def concreteCNF : CNF Nat := indexedCNF 197 inputClause
/-- Input SHA256: 41c481646ea73bb49c2a47c943c3f3c84cc921534990d1be7f5324307dff2397; LRAT SHA256: 72832094a1ee47d5d07e233f50542a772ca7c8e4ffbdc0575d00b3620fe03f4f. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 197 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_0
