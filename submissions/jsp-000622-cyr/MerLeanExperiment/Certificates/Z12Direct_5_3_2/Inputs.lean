import MerLeanExperiment.Certificates.Z12Direct_5_3_2.Clauses0000_0112

/-! Generated from the actual pinned z12direct_5_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through113. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 113 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 113 inputClause
def concreteCNF : CNF Nat := indexedCNF 113 inputClause
/-- Input SHA256: bc4de4818e553521ef5bf352230baf4c765b27c469917a3ab92e65cfab201086; LRAT SHA256: 97a8a241f170503a9a2ee6d58183c6fc68608a26801eddec62f20c915e62c127. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 113 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_2
