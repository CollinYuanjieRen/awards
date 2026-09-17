import MerLeanExperiment.Certificates.Z12Direct_4_1_5.Clauses0000_0098

/-! Generated from the actual pinned z12direct_4_1_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through99. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 99 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 99 inputClause
def concreteCNF : CNF Nat := indexedCNF 99 inputClause
/-- Input SHA256: 024af852697a2fcf9bf1b7b6d5f08d667b92f4238b63c77ebb89a0c3c5d9b988; LRAT SHA256: d6dee4f8620afe1fc7fbd86a14ccacaafe1a27f9ac27262b8ca48a3e8367b2b8. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 99 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_5
