import MerLeanExperiment.Certificates.Z12Direct_5_2_3.Clauses0000_0095

/-! Generated from the actual pinned z12direct_5_2_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through96. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 96 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 96 inputClause
def concreteCNF : CNF Nat := indexedCNF 96 inputClause
/-- Input SHA256: ae21836de024b96251e6a4691ce0497503e6efab4458bc3d6017f4d5bd815f41; LRAT SHA256: 87a05bdb1382fff4ca115a2e6c9f3fc04bb9acc0c13d5e15274a79921e7554cc. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 96 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_2_3
