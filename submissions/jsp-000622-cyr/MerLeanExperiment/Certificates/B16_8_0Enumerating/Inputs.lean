import MerLeanExperiment.Certificates.B16_8_0Enumerating.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_8_0Enumerating.Clauses0250_0417

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through418. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 418 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 418 inputClause
def concreteCNF : CNF Nat := indexedCNF 418 inputClause
/-- Input SHA256: 1fddd26bfdc1d76620c88813a2d1a51f9b6473c15227c07204e7fe75e69e8080; LRAT SHA256: 88e9e27cec444ecc4d9cc787350dbb3c1a00c28124c8884b98b472289b460295. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 418 inputClause a h

end CochromaticTwenty.Certificates.B16_8_0Enumerating
