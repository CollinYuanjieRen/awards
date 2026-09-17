import MerLeanExperiment.Certificates.Z12Direct_5_1_3.Clauses0000_0119

/-! Generated from the actual pinned z12direct_5_1_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through120. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 120 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 120 inputClause
def concreteCNF : CNF Nat := indexedCNF 120 inputClause
/-- Input SHA256: e16111a8afe6e79e66ca5b8aa9a732262292c73b94fd4ddd3bfc6789c41a7b01; LRAT SHA256: bc902496b9af5e9c4f9d62a268e20af142d30df627b4da8e8afdda096b5c0fca. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 120 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_1_3
