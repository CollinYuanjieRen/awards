import MerLeanExperiment.Certificates.Z12Direct_5_5_0.Clauses0000_0128

/-! Generated from the actual pinned z12direct_5_5_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through129. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 129 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 129 inputClause
def concreteCNF : CNF Nat := indexedCNF 129 inputClause
/-- Input SHA256: 2b93185c3932b143154c03939b9c5910b6bec73365b07c1e27a73a004309a330; LRAT SHA256: 04834e9a3ff47ae28f396d25bd6408a51580e4818b579a6275acc58d13f99ef2. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 129 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_0
