import MerLeanExperiment.Certificates.Z12Direct_5_4_6.Clauses0000_0188

/-! Generated from the actual pinned z12direct_5_4_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through189. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 189 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 189 inputClause
def concreteCNF : CNF Nat := indexedCNF 189 inputClause
/-- Input SHA256: d1f9b0e067a3d3c64e5501d27deb4ed1173772d06847d97698d2f0c305922085; LRAT SHA256: c78688540598639854e323ccb2c24315b917a035fa69120ced80cdcd6e705521. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 189 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_6
