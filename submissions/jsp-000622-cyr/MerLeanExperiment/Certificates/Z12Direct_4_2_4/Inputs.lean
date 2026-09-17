import MerLeanExperiment.Certificates.Z12Direct_4_2_4.Clauses0000_0013

/-! Generated from the actual pinned z12direct_4_2_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through14. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 14 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 14 inputClause
def concreteCNF : CNF Nat := indexedCNF 14 inputClause
/-- Input SHA256: b2c19348724614b94b594b7cc901c3677018c6ecb4fc98d48e6fa2de872d4e80; LRAT SHA256: 7c566859867b886fb9b4a267d0ed4fd98b28fae291508ca2d3aa5223a142fa64. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 14 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_4
