import MerLeanExperiment.Certificates.Z12Direct_5_3_12.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_3_12.Clauses0250_0290

/-! Generated from the actual pinned z12direct_5_3_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through291. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 291 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 291 inputClause
def concreteCNF : CNF Nat := indexedCNF 291 inputClause
/-- Input SHA256: e23522fc6487465924f24fc39289d3d5b3178e969286c4feda3871c8738c16a5; LRAT SHA256: d2d22ab12a73a97e8d90b73b1c9660d2e16b30c84bb714d10cf445deb8a10017. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 291 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_12
