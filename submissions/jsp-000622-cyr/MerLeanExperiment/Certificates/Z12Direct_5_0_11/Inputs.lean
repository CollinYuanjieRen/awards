import MerLeanExperiment.Certificates.Z12Direct_5_0_11.Clauses0000_0146

/-! Generated from the actual pinned z12direct_5_0_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through147. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 147 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 147 inputClause
def concreteCNF : CNF Nat := indexedCNF 147 inputClause
/-- Input SHA256: e41a4c3c56e7f2da1ca4a6cd5ae033937973d50951bd8a590e2323dfaefe0638; LRAT SHA256: cc553d2049db4042452be6375401d726fb8cb3bbcca852439f8aff3440ada9dc. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 147 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_11
