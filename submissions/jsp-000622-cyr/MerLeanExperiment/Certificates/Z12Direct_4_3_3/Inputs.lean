import MerLeanExperiment.Certificates.Z12Direct_4_3_3.Clauses0000_0055

/-! Generated from the actual pinned z12direct_4_3_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through56. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 56 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 56 inputClause
def concreteCNF : CNF Nat := indexedCNF 56 inputClause
/-- Input SHA256: bf02710a233301deb9542b8942fb521ed8bab6af3e7d6b2d565346e36e48fe07; LRAT SHA256: 8aecd489abf3e00447b7294dfd50bb1e220b6ca9ef72bd5087b045ee1389f327. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 56 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_3
