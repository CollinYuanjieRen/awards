import MerLeanExperiment.Certificates.Z12Direct_4_5_6.Clauses0000_0025

/-! Generated from the actual pinned z12direct_4_5_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through26. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 26 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 26 inputClause
def concreteCNF : CNF Nat := indexedCNF 26 inputClause
/-- Input SHA256: b72c3ad3cb8f25705c045f9aaa5bd2f3089104a654f4610de6d60cb791b90fba; LRAT SHA256: 6d2fa92d4235c0a0f44699a6d440d6d41740fd29ab11304adfbbde00d56e8dee. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 26 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_5_6
