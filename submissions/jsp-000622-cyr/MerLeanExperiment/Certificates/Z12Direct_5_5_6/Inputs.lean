import MerLeanExperiment.Certificates.Z12Direct_5_5_6.Clauses0000_0163

/-! Generated from the actual pinned z12direct_5_5_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through164. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 164 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 164 inputClause
def concreteCNF : CNF Nat := indexedCNF 164 inputClause
/-- Input SHA256: 49244bef8f501e481123ac9ad6acbaf4c6d35f9047ac05fd67a28f9afdb02907; LRAT SHA256: c67efb962cd7b4fefd6e4f07aae4e86e2ae4651bb6d021ee66a33825fb710038. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 164 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_6
