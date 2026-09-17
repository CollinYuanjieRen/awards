import MerLeanExperiment.Certificates.Z12Direct_5_0_0.Clauses0000_0123

/-! Generated from the actual pinned z12direct_5_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through124. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 124 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 124 inputClause
def concreteCNF : CNF Nat := indexedCNF 124 inputClause
/-- Input SHA256: 229ce02173f2ccf348ea4d4e919e441ab5b38ac6920a41574abc2e72e21a4a21; LRAT SHA256: 5486bee0b7def31cd8c3bacf343cfb5da0b9c90bc4fb9b6a1c0cd509a5fa0c7f. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 124 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_0
