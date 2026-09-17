import MerLeanExperiment.Certificates.Z12Direct_4_3_7.Clauses0000_0056

/-! Generated from the actual pinned z12direct_4_3_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through57. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 57 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 57 inputClause
def concreteCNF : CNF Nat := indexedCNF 57 inputClause
/-- Input SHA256: 193f5a8dfcf9530bfb92dbc95242e2fd8e3fccad7f46200abd40a66db6da188f; LRAT SHA256: 97f25381b260bdbd3ef6b572a14816acf0c0074e810336acadd23203ccbfcd8e. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 57 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_3_7
