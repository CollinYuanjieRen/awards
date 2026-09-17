import MerLeanExperiment.Certificates.Z12Direct_5_0_12.Clauses0000_0129

/-! Generated from the actual pinned z12direct_5_0_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through130. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 130 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 130 inputClause
def concreteCNF : CNF Nat := indexedCNF 130 inputClause
/-- Input SHA256: 63213ed0762d53177051f2deeaa0431efff24e135796575503aa958101ee6865; LRAT SHA256: 1524c698b44667301a4f95db8b4361f9b261ad5023eb0c7c0cae89480c513b5d. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 130 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_12
