import MerLeanExperiment.Certificates.Z12Direct_4_0_0.Clauses0000_0053

/-! Generated from the actual pinned z12direct_4_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through54. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 54 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 54 inputClause
def concreteCNF : CNF Nat := indexedCNF 54 inputClause
/-- Input SHA256: 1bba3e7e523425f08247499507d9eb5e277e3821a0a8695e66c642e6c6694bb4; LRAT SHA256: 93066eaec874a4ecfd4c91398bb3dea44080f77e6125198186936cc0fa6255b3. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 54 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_0
