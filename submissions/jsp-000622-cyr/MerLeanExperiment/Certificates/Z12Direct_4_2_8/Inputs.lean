import MerLeanExperiment.Certificates.Z12Direct_4_2_8.Clauses0000_0196

/-! Generated from the actual pinned z12direct_4_2_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through197. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 197 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 197 inputClause
def concreteCNF : CNF Nat := indexedCNF 197 inputClause
/-- Input SHA256: 61501b4fa211455e21a7a11df766418c396da6fb8b39ddfead50e8bfab424992; LRAT SHA256: 1b5ffbed0ca58b1c28470ee28ea3c3d36878ad36424307e884b33a56bbd57e0e. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 197 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_8
