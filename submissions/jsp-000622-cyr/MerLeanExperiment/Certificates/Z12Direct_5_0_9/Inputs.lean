import MerLeanExperiment.Certificates.Z12Direct_5_0_9.Clauses0000_0183

/-! Generated from the actual pinned z12direct_5_0_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through184. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 184 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 184 inputClause
def concreteCNF : CNF Nat := indexedCNF 184 inputClause
/-- Input SHA256: dc881a59553fb241121cdec92e8b2fd3a280453500d42e52fe01ed410eac5889; LRAT SHA256: 8420f211359b76524336e775391f2e25231b7d3a19eedaa551b8cdf7c797e335. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 184 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_9
