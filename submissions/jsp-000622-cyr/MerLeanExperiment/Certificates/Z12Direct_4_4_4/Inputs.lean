import MerLeanExperiment.Certificates.Z12Direct_4_4_4.Clauses0000_0175

/-! Generated from the actual pinned z12direct_4_4_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through176. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 176 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 176 inputClause
def concreteCNF : CNF Nat := indexedCNF 176 inputClause
/-- Input SHA256: a2c25ced6c1f643a1901a9da06eb0416f3ead4329b5669cf29442b7449343336; LRAT SHA256: 5b345bc98639a01bd27f36a6495fcecafd02d40c1056c6314709887424a3caad. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 176 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_4
