import MerLeanExperiment.Certificates.Z12Direct_3_1_1.Clauses0000_0005

/-! Generated from the actual pinned z12direct_3_1_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through6. -/
def inputClause (id : Nat) : DefaultClause 9 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 9 → Bool) : Prop :=
  ∀ i, i < 6 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 9 := indexedFormula 6 inputClause
def concreteCNF : CNF Nat := indexedCNF 6 inputClause
/-- Input SHA256: fb565b9147b2b9c8e79a013b5c500ab307d936f7690871786c5188acdbfa5381; LRAT SHA256: a1dc5713501c0a25f2e84a8735830ef60c465101ca09de00b37f7fb1c3774831. -/
theorem initialFormula_supplies_inputs (a : PosFin 9 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 6 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_1_1
