import MerLeanExperiment.Certificates.Z12Direct_3_2_0.Clauses0000_0008

/-! Generated from the actual pinned z12direct_3_2_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_2_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through9. -/
def inputClause (id : Nat) : DefaultClause 17 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 17 → Bool) : Prop :=
  ∀ i, i < 9 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 17 := indexedFormula 9 inputClause
def concreteCNF : CNF Nat := indexedCNF 9 inputClause
/-- Input SHA256: dc97b57016980d5ea465186f14330e815f014dc8baaa4ae8b28a895f82c28544; LRAT SHA256: f64541bfcfd57865e6a3aa30d04250a1406a7372a1d1143d6635682d7de4c112. -/
theorem initialFormula_supplies_inputs (a : PosFin 17 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 9 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_2_0
