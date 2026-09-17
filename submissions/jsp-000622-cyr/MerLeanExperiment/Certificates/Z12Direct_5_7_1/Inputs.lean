import MerLeanExperiment.Certificates.Z12Direct_5_7_1.Clauses0000_0158

/-! Generated from the actual pinned z12direct_5_7_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through159. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 159 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 159 inputClause
def concreteCNF : CNF Nat := indexedCNF 159 inputClause
/-- Input SHA256: 57291239007dec640dbdff9526012f828368624747f62bd2c222aa6939cd1b2d; LRAT SHA256: 72e4b99190c03fcfba48db936bb1669ab86bda984b1cb7fc0cc7d636ef442dce. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 159 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_1
