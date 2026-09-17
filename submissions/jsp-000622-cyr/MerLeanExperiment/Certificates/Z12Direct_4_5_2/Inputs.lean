import MerLeanExperiment.Certificates.Z12Direct_4_5_2.Clauses0000_0090

/-! Generated from the actual pinned z12direct_4_5_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through91. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 91 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 91 inputClause
def concreteCNF : CNF Nat := indexedCNF 91 inputClause
/-- Input SHA256: 1e4cf5301a12ad9bb61f9e3720eb3252d80f5738395b80950f8a8f95d17fb2fa; LRAT SHA256: a750ac7654a077e7ee9805036cc2c96b2612b17afe2b2107abd2308637dd0a9b. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 91 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_2
