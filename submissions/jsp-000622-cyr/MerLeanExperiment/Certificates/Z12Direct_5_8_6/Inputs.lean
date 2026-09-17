import MerLeanExperiment.Certificates.Z12Direct_5_8_6.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_6.Clauses0250_0324

/-! Generated from the actual pinned z12direct_5_8_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through325. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 325 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 325 inputClause
def concreteCNF : CNF Nat := indexedCNF 325 inputClause
/-- Input SHA256: 22b82f1c3e0e2497f1baf5272d2c659054509ab2a304f0c8c2d1b1bfdaf4c3ca; LRAT SHA256: cdf01cb9061efacd4e13e70d9ec773ad2802955e7ef36bf424cf306a3bc3e674. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 325 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_6
