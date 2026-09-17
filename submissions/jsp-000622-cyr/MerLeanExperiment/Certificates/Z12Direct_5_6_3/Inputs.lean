import MerLeanExperiment.Certificates.Z12Direct_5_6_3.Clauses0000_0045

/-! Generated from the actual pinned z12direct_5_6_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through46. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 46 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 46 inputClause
def concreteCNF : CNF Nat := indexedCNF 46 inputClause
/-- Input SHA256: f4e6f46d5f99858f8605fde6615f8e219db815be9dfc6d0ee4fffac1a737188c; LRAT SHA256: a670edff1b1a25e93b86b684d1383b413e408da846a501424a357f107977b11e. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 46 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_3
