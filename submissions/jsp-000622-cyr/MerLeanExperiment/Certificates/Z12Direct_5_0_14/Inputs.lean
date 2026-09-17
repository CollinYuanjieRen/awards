import MerLeanExperiment.Certificates.Z12Direct_5_0_14.Clauses0000_0066

/-! Generated from the actual pinned z12direct_5_0_14-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_14
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through67. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 67 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 67 inputClause
def concreteCNF : CNF Nat := indexedCNF 67 inputClause
/-- Input SHA256: 2262f8eb63bd8cd139be194bee740235f453dbef5a013af4f25449cf85df76e2; LRAT SHA256: 9bf68f562d6c9477a12ce82630456931ba027939d3021deb93dd1796066c42e5. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 67 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_14
