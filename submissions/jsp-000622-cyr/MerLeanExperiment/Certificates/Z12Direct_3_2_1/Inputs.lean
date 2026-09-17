import MerLeanExperiment.Certificates.Z12Direct_3_2_1.Clauses0000_0005

/-! Generated from the actual pinned z12direct_3_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through6. -/
def inputClause (id : Nat) : DefaultClause 17 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 17 → Bool) : Prop :=
  ∀ i, i < 6 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 17 := indexedFormula 6 inputClause
def concreteCNF : CNF Nat := indexedCNF 6 inputClause
/-- Input SHA256: 43d81ead0d4ff2e8e06886272433cabd366023ebe6d9a808df2bf21acfb932f5; LRAT SHA256: 80c3bb98fbe363b9d17307de4ebc7eaa6214b6dc1e2ce622508d4988aca6898c. -/
theorem initialFormula_supplies_inputs (a : PosFin 17 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 6 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_2_1
