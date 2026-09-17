import MerLeanExperiment.Certificates.Z12Direct_5_7_2.Clauses0000_0089

/-! Generated from the actual pinned z12direct_5_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through90. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 90 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 90 inputClause
def concreteCNF : CNF Nat := indexedCNF 90 inputClause
/-- Input SHA256: 30adfc1cda501e399231c893ae661ff7fba71e1446e2dfdc9465c8e2689be053; LRAT SHA256: 934cddfd882acea65001aff9e8d1d1b1d1188d8961e70e5654b1fbfaf8dfc0ef. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 90 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_2
