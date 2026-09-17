import MerLeanExperiment.Certificates.Z12Direct_5_0_5.Clauses0000_0126

/-! Generated from the actual pinned z12direct_5_0_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through127. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 127 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 127 inputClause
def concreteCNF : CNF Nat := indexedCNF 127 inputClause
/-- Input SHA256: 8f00c3cbb7821c19c3ee7fc77fb1da5087903a78b6217da1391e31805335f4b0; LRAT SHA256: aaf62d3986d057c864b61e860f3434117d5f8ed369a9174348bddad9cbdbeff0. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 127 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_5
