import MerLeanExperiment.Certificates.Z12Direct_4_2_3.Clauses0000_0018

/-! Generated from the actual pinned z12direct_4_2_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through19. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 19 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 19 inputClause
def concreteCNF : CNF Nat := indexedCNF 19 inputClause
/-- Input SHA256: 89e1e72ed8cbd7d853f3722e8199e26a73b76b1c977a9f93829352d11190db4b; LRAT SHA256: 529c345448d676634dd11419cb83e6eadaefd9db22e06639c8cc4b41dfc285be. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 19 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_3
