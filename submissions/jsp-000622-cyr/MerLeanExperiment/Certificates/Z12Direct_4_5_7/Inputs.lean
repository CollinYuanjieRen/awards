import MerLeanExperiment.Certificates.Z12Direct_4_5_7.Clauses0000_0017

/-! Generated from the actual pinned z12direct_4_5_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through18. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 18 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 18 inputClause
def concreteCNF : CNF Nat := indexedCNF 18 inputClause
/-- Input SHA256: 17bf8fc21b2d882a97bcf9e3058529f09846b30dbe4a06976d675bfaa44ffec3; LRAT SHA256: e31e0f7d96efe95fe830675e108420134cc73d8ea510a2ef006cdd3e4894123f. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 18 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_7
