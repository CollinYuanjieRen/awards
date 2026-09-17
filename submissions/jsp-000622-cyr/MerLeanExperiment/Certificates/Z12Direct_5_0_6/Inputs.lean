import MerLeanExperiment.Certificates.Z12Direct_5_0_6.Clauses0000_0120

/-! Generated from the actual pinned z12direct_5_0_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through121. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 121 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 121 inputClause
def concreteCNF : CNF Nat := indexedCNF 121 inputClause
/-- Input SHA256: ff62fc0ec7982bbc7dbee9ce425dcdecd1e794e4404dc4a09d38f992582862df; LRAT SHA256: cea735c37ac811e986218aa761d4c1ddec586e7ed1bca76d1eb34d978b105653. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 121 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_6
