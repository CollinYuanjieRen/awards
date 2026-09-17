import MerLeanExperiment.Certificates.Z12Direct_4_0_5.Clauses0000_0110

/-! Generated from the actual pinned z12direct_4_0_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through111. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 111 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 111 inputClause
def concreteCNF : CNF Nat := indexedCNF 111 inputClause
/-- Input SHA256: cf342f98b5e820f94371adb4ce703b6d118b29eff5261d80b85f3d1d51eeefdc; LRAT SHA256: 584b6b33f097c60cd342dbe78bc01077ffe412ddf0ecd9065e568daf80ebca9c. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 111 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_0_5
