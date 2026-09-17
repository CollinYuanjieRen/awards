import MerLeanExperiment.Certificates.Z12Direct_4_4_1.Clauses0000_0093

/-! Generated from the actual pinned z12direct_4_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through94. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 94 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 94 inputClause
def concreteCNF : CNF Nat := indexedCNF 94 inputClause
/-- Input SHA256: ecee7e3f6561258ff40387f3b807c51395146d830c839586738fdaa93c1f11c9; LRAT SHA256: d2edef8cead33b34447e5b312dbe1f00b45645e7545a53c91db7e97ec0bf2c02. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 94 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_1
