import MerLeanExperiment.Certificates.Z12Direct_5_6_13.Clauses0000_0195

/-! Generated from the actual pinned z12direct_5_6_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through196. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 196 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 196 inputClause
def concreteCNF : CNF Nat := indexedCNF 196 inputClause
/-- Input SHA256: be7434fcca762f67144ffbfcba37465a541f0689e64457875c12ddf0bc15c4c1; LRAT SHA256: 56e2604450c10ace06d29bd85307fc7eef32c963262585e906421bc5bb00b9bf. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 196 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_13
