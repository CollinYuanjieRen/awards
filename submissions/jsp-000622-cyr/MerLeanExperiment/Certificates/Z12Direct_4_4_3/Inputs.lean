import MerLeanExperiment.Certificates.Z12Direct_4_4_3.Clauses0000_0152

/-! Generated from the actual pinned z12direct_4_4_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through153. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 153 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 153 inputClause
def concreteCNF : CNF Nat := indexedCNF 153 inputClause
/-- Input SHA256: 4a19ac02374d0013a5e23d2b3b92aa862569d1e3845e05b461a5498686a452e3; LRAT SHA256: f932772999a7bd9d0371bb5738fff4e79ab9358954b82e87996e379bf68d84aa. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 153 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_3
