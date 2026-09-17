import MerLeanExperiment.Certificates.Z12Direct_4_4_7.Clauses0000_0074

/-! Generated from the actual pinned z12direct_4_4_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through75. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 75 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 75 inputClause
def concreteCNF : CNF Nat := indexedCNF 75 inputClause
/-- Input SHA256: a787e54cb1901a42d4f8118f5b4d29fa601709ee3701823f16ee11b2163b4a0c; LRAT SHA256: 1e36fd941990416afec54b991f6414c084875e1b69f9464e2d461e3a1857e868. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 75 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_7
