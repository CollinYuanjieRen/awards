import MerLeanExperiment.Certificates.Z12Direct_5_4_3.Clauses0000_0139

/-! Generated from the actual pinned z12direct_5_4_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through140. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 140 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 140 inputClause
def concreteCNF : CNF Nat := indexedCNF 140 inputClause
/-- Input SHA256: 6a2ca99e635a08ffeca97adabe7cfe269bdf322610766c3e125320706999a733; LRAT SHA256: b4fddbc2e5210514849b65433e2ab28964f72dd184f57b3ef1a86141adfd7af0. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 140 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_3
