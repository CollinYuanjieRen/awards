import MerLeanExperiment.Certificates.Z12Direct_5_8_0.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_0.Clauses0250_0326

/-! Generated from the actual pinned z12direct_5_8_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through327. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 327 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 327 inputClause
def concreteCNF : CNF Nat := indexedCNF 327 inputClause
/-- Input SHA256: d579e3376f471db6cc83eded3c6a6ec7562f6711f0ef889c1d2a37e6603ddf95; LRAT SHA256: 0bc14a65812808baa97622485a26870ab756ca2f7b43acbd3a024b4bc209b73f. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 327 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_0
