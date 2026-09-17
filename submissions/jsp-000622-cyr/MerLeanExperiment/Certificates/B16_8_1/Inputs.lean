import MerLeanExperiment.Certificates.B16_8_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_8_1.Clauses0250_0287

/-! Generated from the actual pinned b16_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through288. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 288 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 288 inputClause
def concreteCNF : CNF Nat := indexedCNF 288 inputClause
/-- Input SHA256: 3d70c4353c452ae9892c974d9bd0cb587ac1972290067d7bb241e6e439c82cf8; LRAT SHA256: ce76e6d7c534aa7e21647e8ef1d78b9d6352681e0ab6ba65a14ca6df9c76d5c5. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 288 inputClause a h

end CochromaticTwenty.Certificates.B16_8_1
