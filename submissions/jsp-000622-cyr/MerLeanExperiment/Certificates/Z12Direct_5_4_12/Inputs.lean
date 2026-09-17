import MerLeanExperiment.Certificates.Z12Direct_5_4_12.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_4_12.Clauses0250_0287

/-! Generated from the actual pinned z12direct_5_4_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through288. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 288 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 288 inputClause
def concreteCNF : CNF Nat := indexedCNF 288 inputClause
/-- Input SHA256: b0413f4a07d1577543de3155f76e2ba2140fc87c992f53e9a2bf726ec56b9335; LRAT SHA256: 54dc046bff604e091c0b5c6b4cbe1f0f55263683f873a55ba19fd8126c1b57a8. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 288 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_12
