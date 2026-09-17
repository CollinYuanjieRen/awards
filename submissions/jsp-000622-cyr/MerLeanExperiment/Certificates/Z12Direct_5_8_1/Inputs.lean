import MerLeanExperiment.Certificates.Z12Direct_5_8_1.Clauses0000_0239

/-! Generated from the actual pinned z12direct_5_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through240. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 240 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 240 inputClause
def concreteCNF : CNF Nat := indexedCNF 240 inputClause
/-- Input SHA256: 16b4cdeb05b9c55248a267aa71cecfd60b77fe719908568e0d41c358b066b54e; LRAT SHA256: 7e7df345f89582f7ed6651ec3939e7bf07f5656022bf53754ac5ac0ed2b8c59d. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 240 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_1
