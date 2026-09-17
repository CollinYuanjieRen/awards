import MerLeanExperiment.Certificates.Z12Direct_4_3_6.Clauses0000_0025

/-! Generated from the actual pinned z12direct_4_3_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through26. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 26 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 26 inputClause
def concreteCNF : CNF Nat := indexedCNF 26 inputClause
/-- Input SHA256: 47a16ac2c47501cd4c2c05897dda0a35e33889bc92f869de702ebd0fc8c0cf4a; LRAT SHA256: dece2b269e1a42f342a7f9853c1cf00b63e1540b2ee926381c8f7be4bfbfb947. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 26 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_6
