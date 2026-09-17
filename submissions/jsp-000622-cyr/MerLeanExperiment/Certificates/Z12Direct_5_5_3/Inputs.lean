import MerLeanExperiment.Certificates.Z12Direct_5_5_3.Clauses0000_0109

/-! Generated from the actual pinned z12direct_5_5_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through110. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 110 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 110 inputClause
def concreteCNF : CNF Nat := indexedCNF 110 inputClause
/-- Input SHA256: 760b6764a8948548517d1afb4a482bf28de5e0e69167b1deaf31a03c029796c8; LRAT SHA256: ae42f8ed14659d05ff3e256eb420c8b12d646a0c3bba786e7aeff74aa44ffc2b. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 110 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_3
