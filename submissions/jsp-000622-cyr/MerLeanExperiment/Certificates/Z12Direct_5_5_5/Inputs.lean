import MerLeanExperiment.Certificates.Z12Direct_5_5_5.Clauses0000_0119

/-! Generated from the actual pinned z12direct_5_5_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through120. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 120 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 120 inputClause
def concreteCNF : CNF Nat := indexedCNF 120 inputClause
/-- Input SHA256: 186192b382b424a2187287c61c521323ab0cd6ffef0c32bfe14aecc1ab2c9260; LRAT SHA256: 32c7764887870b75265e2812aaff6c7f50f1521c8055e81dffdaf389a297dfed. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 120 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_5
