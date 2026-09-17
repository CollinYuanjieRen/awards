import MerLeanExperiment.Certificates.Z12Direct_5_0_8.Clauses0000_0122

/-! Generated from the actual pinned z12direct_5_0_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through123. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 123 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 123 inputClause
def concreteCNF : CNF Nat := indexedCNF 123 inputClause
/-- Input SHA256: a7e27d494b4ded3c05d51425174f1dcb8ff6e0af8b5be232a533bc538b6e203a; LRAT SHA256: 62371d44997d0d47c95a4c447cec7e167f27cf81130542ddd8ebb9ba908e0658. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 123 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_8
