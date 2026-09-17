import MerLeanExperiment.Certificates.Z12Direct_5_6_9.Clauses0000_0146

/-! Generated from the actual pinned z12direct_5_6_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through147. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 147 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 147 inputClause
def concreteCNF : CNF Nat := indexedCNF 147 inputClause
/-- Input SHA256: 2cf1b44b3451fd34d5b5ed455882664f3d5d9de0dd461d676bb557dd0e86862a; LRAT SHA256: 0f49a08413e5fc2027280f5bdb6088ebf8e5f12bda26498445949c019e5894c4. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 147 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_9
