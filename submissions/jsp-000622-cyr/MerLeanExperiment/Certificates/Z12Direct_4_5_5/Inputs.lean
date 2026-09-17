import MerLeanExperiment.Certificates.Z12Direct_4_5_5.Clauses0000_0083

/-! Generated from the actual pinned z12direct_4_5_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through84. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 84 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 84 inputClause
def concreteCNF : CNF Nat := indexedCNF 84 inputClause
/-- Input SHA256: b6a73245895f16e299c0c9357ee5d9cd39499f24cb1438124eb3942d38f235e8; LRAT SHA256: d810d4247917c27f34158493b3c8dc73b3e33f5af35b6b8911f9eb1009f0a4d4. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 84 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_5
