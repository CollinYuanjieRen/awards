import MerLeanExperiment.Certificates.Z12Direct_5_4_4.Clauses0000_0198

/-! Generated from the actual pinned z12direct_5_4_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through199. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 199 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 199 inputClause
def concreteCNF : CNF Nat := indexedCNF 199 inputClause
/-- Input SHA256: 599360e48bc80ad3b1580fe024e189bc4d62dfefad810267bdafe19f8c725c31; LRAT SHA256: 4c68e3d433d8339739b3119c3cc927cf5f6e367daf8e63c52213e838ead0ce32. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 199 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_4
