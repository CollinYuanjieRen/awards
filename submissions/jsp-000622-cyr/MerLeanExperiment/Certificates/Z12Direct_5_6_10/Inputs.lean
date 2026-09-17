import MerLeanExperiment.Certificates.Z12Direct_5_6_10.Clauses0000_0041

/-! Generated from the actual pinned z12direct_5_6_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through42. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 42 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 42 inputClause
def concreteCNF : CNF Nat := indexedCNF 42 inputClause
/-- Input SHA256: 0cda86174f67595fc7e61abeea1dbf0186d0fdf24cdade78c073c72a644f4daa; LRAT SHA256: 1dc43dfb265ef116b8aa691e51bddc2889eb5362d1157ebcab93737c133d5be8. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 42 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_10
