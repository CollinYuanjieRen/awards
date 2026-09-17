import MerLeanExperiment.Certificates.Z12Direct_5_4_8.Clauses0000_0160

/-! Generated from the actual pinned z12direct_5_4_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through161. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 161 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 161 inputClause
def concreteCNF : CNF Nat := indexedCNF 161 inputClause
/-- Input SHA256: fcef447c1d0a05c1843cb2ff27e293b595d46a4de3184ddace45c4a9a3eb6634; LRAT SHA256: 26415ef9690a64a862f8c30e26a4adb36c7c82942e88a62314c933c2c2e8bdcf. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 161 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_8
