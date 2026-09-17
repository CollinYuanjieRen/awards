import MerLeanExperiment.Certificates.Z12Direct_4_2_5.Clauses0000_0043

/-! Generated from the actual pinned z12direct_4_2_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through44. -/
def inputClause (id : Nat) : DefaultClause 22 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 22 → Bool) : Prop :=
  ∀ i, i < 44 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 22 := indexedFormula 44 inputClause
def concreteCNF : CNF Nat := indexedCNF 44 inputClause
/-- Input SHA256: cde3f8e1f4e89d2a25c3c7d6f58adadc4c600433dc85270d993f9a70fe1559d8; LRAT SHA256: 139f169ca64f3aed4cd76f061fe3f47a5df4b039f1ef82dd36629f7364e5e012. -/
theorem initialFormula_supplies_inputs (a : PosFin 22 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 44 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_5
