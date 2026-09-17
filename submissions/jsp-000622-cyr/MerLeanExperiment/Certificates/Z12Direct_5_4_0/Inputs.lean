import MerLeanExperiment.Certificates.Z12Direct_5_4_0.Clauses0000_0187

/-! Generated from the actual pinned z12direct_5_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through188. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 188 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 188 inputClause
def concreteCNF : CNF Nat := indexedCNF 188 inputClause
/-- Input SHA256: bd36b8241ecf2173930b452ca12ec0bfc2901f6a9e99c8f84974dbd2aafd0224; LRAT SHA256: bed61c841d113d060368e92b4045a5ab5fe15864c8ba4d82dedce83406dbb53a. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 188 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_0
