import MerLeanExperiment.Certificates.Z12Direct_5_1_6.Clauses0000_0124

/-! Generated from the actual pinned z12direct_5_1_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through125. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 125 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 125 inputClause
def concreteCNF : CNF Nat := indexedCNF 125 inputClause
/-- Input SHA256: 0bebfbefa3da229b224c9d2604e5816351c37cf4166f04a42810e8c1bae2a6c5; LRAT SHA256: 1f64284216b882ffc62fb2819f392d08671554ad118338cb7781494e6c0fcd59. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 125 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_1_6
