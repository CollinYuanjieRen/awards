import MerLeanExperiment.Certificates.Z12Direct_4_1_4.Clauses0000_0039

/-! Generated from the actual pinned z12direct_4_1_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through40. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 40 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 40 inputClause
def concreteCNF : CNF Nat := indexedCNF 40 inputClause
/-- Input SHA256: a7a3a85324acb551c9168222193e794601714da5e59e0c6d761fc7bca1b3fb1c; LRAT SHA256: f8b31b40d6af5940005f1c11dde793a3c1c1a90e0ace0b6a37f6fb2d3a8d0432. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 40 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_4
