import MerLeanExperiment.Certificates.Z12Direct_4_1_2.Clauses0000_0104

/-! Generated from the actual pinned z12direct_4_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through105. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 105 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 105 inputClause
def concreteCNF : CNF Nat := indexedCNF 105 inputClause
/-- Input SHA256: 829a0a1f582511b2de37cd3edd432c7f80109700b7adec3a3e8abe8089521025; LRAT SHA256: 26d4a02892514b1787169ca882cf39b428f0a2024d089fb99f1e6c6fcaf4d9a6. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 105 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_2
