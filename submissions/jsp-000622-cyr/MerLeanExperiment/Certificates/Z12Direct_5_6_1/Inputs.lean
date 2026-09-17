import MerLeanExperiment.Certificates.Z12Direct_5_6_1.Clauses0000_0107

/-! Generated from the actual pinned z12direct_5_6_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through108. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 108 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 108 inputClause
def concreteCNF : CNF Nat := indexedCNF 108 inputClause
/-- Input SHA256: 90097be56939828642f153685457160a8c9165da0ef57827263c04af75ef849a; LRAT SHA256: 27e951d7b8752f97a42c257868dc72fd6be86c2701c39cdf65c616609b98a898. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 108 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_1
