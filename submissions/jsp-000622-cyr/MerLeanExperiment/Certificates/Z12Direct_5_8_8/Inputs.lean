import MerLeanExperiment.Certificates.Z12Direct_5_8_8.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_8.Clauses0250_0333

/-! Generated from the actual pinned z12direct_5_8_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through334. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 334 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 334 inputClause
def concreteCNF : CNF Nat := indexedCNF 334 inputClause
/-- Input SHA256: 72358e7f5a376ca7f483633b40450d945f98470be23444d3d811ad8cb87d105a; LRAT SHA256: 341a8d0298eb36b2bfaa26ac7d5e99a9e8569802f5b20e366820ac6f7bf2f5f7. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 334 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_8
