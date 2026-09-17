import MerLeanExperiment.Certificates.Z12Direct_5_8_10.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_10.Clauses0250_0327

/-! Generated from the actual pinned z12direct_5_8_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through328. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 328 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 328 inputClause
def concreteCNF : CNF Nat := indexedCNF 328 inputClause
/-- Input SHA256: 7b8b51ccbdfd928f27ff487a8b992097aa9fc013661417c25f03f02d909952e6; LRAT SHA256: 78adfc930ba8f2199dff2babd1cb6e6f4d275625912eecc0becd9c1bbcf6c9a5. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 328 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_10
