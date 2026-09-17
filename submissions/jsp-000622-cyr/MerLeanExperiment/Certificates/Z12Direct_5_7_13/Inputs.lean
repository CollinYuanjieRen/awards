import MerLeanExperiment.Certificates.Z12Direct_5_7_13.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_7_13.Clauses0250_0341

/-! Generated from the actual pinned z12direct_5_7_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through342. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 342 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 342 inputClause
def concreteCNF : CNF Nat := indexedCNF 342 inputClause
/-- Input SHA256: dcb6fd4c868746cd6638b9da27c4d2c6a30c4a63d40889594c95c5b9925a211d; LRAT SHA256: d7d65fe430dac82dc556217dca8e8a196b992f5d66be4b65dd88cbfd1649de41. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 342 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_13
