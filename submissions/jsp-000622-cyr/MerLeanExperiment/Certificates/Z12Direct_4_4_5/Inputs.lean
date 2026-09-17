import MerLeanExperiment.Certificates.Z12Direct_4_4_5.Clauses0000_0168

/-! Generated from the actual pinned z12direct_4_4_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through169. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 169 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 169 inputClause
def concreteCNF : CNF Nat := indexedCNF 169 inputClause
/-- Input SHA256: 4e55838cd0ddce9b090c0b190ee4226b3fcd0cdbe984080bdf48b2c5e6275ac3; LRAT SHA256: f44512bfb6ef65ae9bbf9152eb4affb90fb4bc3e81e2c3a0bc99176b36978c63. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 169 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_5
