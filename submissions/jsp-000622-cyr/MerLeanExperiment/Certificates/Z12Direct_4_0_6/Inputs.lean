import MerLeanExperiment.Certificates.Z12Direct_4_0_6.Clauses0000_0101

/-! Generated from the actual pinned z12direct_4_0_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through102. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 102 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 102 inputClause
def concreteCNF : CNF Nat := indexedCNF 102 inputClause
/-- Input SHA256: 933470e57eeea049b6e064a45c15fc31ed1736f8f0fc7975e9b84a0c9d042c23; LRAT SHA256: 90ce7268fd12be95b1c7f40b9df76a2502e08fbc8f33858d75f941c252606961. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 102 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_6
