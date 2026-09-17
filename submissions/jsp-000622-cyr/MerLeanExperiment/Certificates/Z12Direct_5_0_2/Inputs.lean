import MerLeanExperiment.Certificates.Z12Direct_5_0_2.Clauses0000_0062

/-! Generated from the actual pinned z12direct_5_0_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through63. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 63 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 63 inputClause
def concreteCNF : CNF Nat := indexedCNF 63 inputClause
/-- Input SHA256: 84107c4c32f1751bc55153ff1aca5cc7db626c6ed95fd55ecebf7af756dd21cb; LRAT SHA256: 2d710578b2db7670cbcf287d2305938641995183ed77597793a4f5afe7af0ff8. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 63 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_2
