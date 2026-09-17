import MerLeanExperiment.Certificates.Z12Direct_4_1_8.Clauses0000_0227

/-! Generated from the actual pinned z12direct_4_1_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through228. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 228 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 228 inputClause
def concreteCNF : CNF Nat := indexedCNF 228 inputClause
/-- Input SHA256: 0bce9491992e057eb127a7f08288d5a2ade220f604566c6485cf4f20c9324340; LRAT SHA256: d9962324d72512135c087071652ea57e837757a18c64421a1ca16f959c8805c0. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 228 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_8
