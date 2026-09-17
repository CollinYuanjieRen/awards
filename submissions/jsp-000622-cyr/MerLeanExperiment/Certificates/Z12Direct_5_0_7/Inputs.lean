import MerLeanExperiment.Certificates.Z12Direct_5_0_7.Clauses0000_0125

/-! Generated from the actual pinned z12direct_5_0_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through126. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 126 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 126 inputClause
def concreteCNF : CNF Nat := indexedCNF 126 inputClause
/-- Input SHA256: 6b3cb9816914e2866eb7c3618f3095144f6b9d0cb31b8f1fee868391330e59c3; LRAT SHA256: 34aa460bcffef2fc4b62f8bfce920b8a661d65601919b6d9845775a687077ea9. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 126 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_7
