import MerLeanExperiment.Certificates.Z12Direct_5_7_14.Clauses0000_0066

/-! Generated from the actual pinned z12direct_5_7_14-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through67. -/
def inputClause (id : Nat) : DefaultClause 25 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 25 → Bool) : Prop :=
  ∀ i, i < 67 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 25 := indexedFormula 67 inputClause
def concreteCNF : CNF Nat := indexedCNF 67 inputClause
/-- Input SHA256: e921b48dc304d1d6866b92f380cc7123dff2bfb73a901ca1492446b17a32f27c; LRAT SHA256: a1c3d50c28779698dab440d8b1a3960f2bff4c2d358347997d80212174298f2f. -/
theorem initialFormula_supplies_inputs (a : PosFin 25 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 67 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_14
