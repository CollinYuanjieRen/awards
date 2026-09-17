import MerLeanExperiment.Certificates.Z12Direct_5_4_1.Clauses0000_0207

/-! Generated from the actual pinned z12direct_5_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through208. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 208 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 208 inputClause
def concreteCNF : CNF Nat := indexedCNF 208 inputClause
/-- Input SHA256: 6f5a124710c829e4573b88f948e58e1eeeb0e86343ff383cb2c5cf37095343fb; LRAT SHA256: ef370f32dd90ec8f28864df1f99b2805c44d28cb3fc5d8cc3aea2127860bfe28. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 208 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_1
