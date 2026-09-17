import MerLeanExperiment.Certificates.Z12Direct_4_2_1.Clauses0000_0013

/-! Generated from the actual pinned z12direct_4_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through14. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 14 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 14 inputClause
def concreteCNF : CNF Nat := indexedCNF 14 inputClause
/-- Input SHA256: 7f5769acd17ac3489b2df9c1249970e1def2911896ef947e1fefa913b9284487; LRAT SHA256: e292285b93ae92d93cf1d55fbae628e69ffecdb8502135cd62816445955cf38e. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 14 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_1
