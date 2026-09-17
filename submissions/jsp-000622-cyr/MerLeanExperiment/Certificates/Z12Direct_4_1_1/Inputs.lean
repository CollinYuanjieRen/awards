import MerLeanExperiment.Certificates.Z12Direct_4_1_1.Clauses0000_0028

/-! Generated from the actual pinned z12direct_4_1_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through29. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 29 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 29 inputClause
def concreteCNF : CNF Nat := indexedCNF 29 inputClause
/-- Input SHA256: 2580b7aab27a54fd663fc019b272f42c9ace6f220e600380d6d83cca5df53a4d; LRAT SHA256: 8b33bdbedbc3bda64189caa7950480c26ea128b12b6d63b7777beafb2146336c. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 29 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_1
