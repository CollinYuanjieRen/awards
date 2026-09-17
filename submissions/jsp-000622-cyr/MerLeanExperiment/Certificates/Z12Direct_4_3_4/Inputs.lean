import MerLeanExperiment.Certificates.Z12Direct_4_3_4.Clauses0000_0118

/-! Generated from the actual pinned z12direct_4_3_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through119. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 119 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 119 inputClause
def concreteCNF : CNF Nat := indexedCNF 119 inputClause
/-- Input SHA256: 8469ea8b33c1756e98d6de8222fcdfe9fac4e06a1d9d639e361346d9d6c5ec39; LRAT SHA256: 5b4796c3ef206956c32933460bda812f0147dba2cab22043924a877d6b88379e. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 119 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_4
