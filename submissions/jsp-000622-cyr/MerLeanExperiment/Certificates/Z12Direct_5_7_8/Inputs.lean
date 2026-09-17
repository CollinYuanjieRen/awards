import MerLeanExperiment.Certificates.Z12Direct_5_7_8.Clauses0000_0183

/-! Generated from the actual pinned z12direct_5_7_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through184. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 184 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 184 inputClause
def concreteCNF : CNF Nat := indexedCNF 184 inputClause
/-- Input SHA256: 2e15ddc1af97f219ada0569ec2f68ed91bd5f9c295809635ccc8aedea050d1ca; LRAT SHA256: e202fe4df7c60ecca81a431a170a12159b7fcd6ebf6dcff3579b28710cc44616. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 184 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_8
