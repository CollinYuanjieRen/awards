import MerLeanExperiment.Certificates.Z12Direct_5_7_12.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_7_12.Clauses0250_0261

/-! Generated from the actual pinned z12direct_5_7_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through262. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 262 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 262 inputClause
def concreteCNF : CNF Nat := indexedCNF 262 inputClause
/-- Input SHA256: 571cfd48484a1324c9bad355cb055a675e06caf17e3b779b1be46a2c1839ab25; LRAT SHA256: b25ec792740d9b1821bcaa4171f582da7bfa0b3ce9e381611b1fe2f1335a9577. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 262 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_12
