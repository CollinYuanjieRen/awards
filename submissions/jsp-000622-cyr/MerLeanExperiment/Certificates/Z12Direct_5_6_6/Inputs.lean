import MerLeanExperiment.Certificates.Z12Direct_5_6_6.Clauses0000_0073

/-! Generated from the actual pinned z12direct_5_6_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through74. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 74 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 74 inputClause
def concreteCNF : CNF Nat := indexedCNF 74 inputClause
/-- Input SHA256: ede8ef2d61a2f8ad7adeb1b188c7d756478f34462da02244744475f7f266bd86; LRAT SHA256: a46e70c107545ef5de5f4e476edb66ea3d0ca60eefb13dcfd9d1dbd666a2d29c. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 74 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_6
