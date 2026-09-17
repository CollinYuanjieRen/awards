import MerLeanExperiment.Certificates.Z12Direct_5_0_13.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_0_13.Clauses0250_0253

/-! Generated from the actual pinned z12direct_5_0_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through254. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 254 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 254 inputClause
def concreteCNF : CNF Nat := indexedCNF 254 inputClause
/-- Input SHA256: 719591aeb0426a898c13e19227dfcc392a8e7e365b727a4376517352e5320db3; LRAT SHA256: 08f107c55335aefbf1965eaf13e3b8756362cfae290a06bdc21dac4da7eae7bb. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 254 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_13
