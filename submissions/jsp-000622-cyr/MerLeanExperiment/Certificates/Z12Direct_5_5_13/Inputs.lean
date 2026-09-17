import MerLeanExperiment.Certificates.Z12Direct_5_5_13.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_5_13.Clauses0250_0401

/-! Generated from the actual pinned z12direct_5_5_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through402. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 402 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 402 inputClause
def concreteCNF : CNF Nat := indexedCNF 402 inputClause
/-- Input SHA256: 1776ce671c522d82d8c3730f877c8d2a19c1ddfae001cec83bd064a1efebd963; LRAT SHA256: 5d9d1e6bea14fb28683806b51d43a3663ddcde37fa5bab6dea9647d32c7424e6. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 402 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_13
