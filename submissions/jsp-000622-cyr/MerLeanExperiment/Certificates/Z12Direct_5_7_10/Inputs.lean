import MerLeanExperiment.Certificates.Z12Direct_5_7_10.Clauses0000_0171

/-! Generated from the actual pinned z12direct_5_7_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through172. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 172 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 172 inputClause
def concreteCNF : CNF Nat := indexedCNF 172 inputClause
/-- Input SHA256: 16bf38047928ddafbbe98e2d6d856b15168fd62abea520859fc256f4a87892f5; LRAT SHA256: a4be1877a6605008f123b1004a554658932b9d8920cc269a74ad09224ccdfe91. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 172 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_10
