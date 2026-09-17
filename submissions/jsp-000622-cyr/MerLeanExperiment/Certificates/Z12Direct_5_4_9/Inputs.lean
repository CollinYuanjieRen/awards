import MerLeanExperiment.Certificates.Z12Direct_5_4_9.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_4_9.Clauses0250_0260

/-! Generated from the actual pinned z12direct_5_4_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through261. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 261 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 261 inputClause
def concreteCNF : CNF Nat := indexedCNF 261 inputClause
/-- Input SHA256: cb665e12ddbdb2d46298466b8ca7d33899230a356fd042fd4b47a7cd36605b78; LRAT SHA256: 439eb6190bde362b03a37c8ae6a9cd8d43494f23a7e63f678c5314a68267ba6f. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 261 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_9
