import MerLeanExperiment.Certificates.Z12Direct_4_3_0.Clauses0000_0105

/-! Generated from the actual pinned z12direct_4_3_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through106. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 106 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 106 inputClause
def concreteCNF : CNF Nat := indexedCNF 106 inputClause
/-- Input SHA256: 782ae82cf419d14569e007b3e59319d250cb94fa62bb57a753aba53285666f40; LRAT SHA256: c706c8d5b9795e080fea24e285c1507fa655a43741a151eafc186427c42a810a. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 106 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_0
