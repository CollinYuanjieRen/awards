import MerLeanExperiment.Certificates.Z12Direct_5_2_9.Clauses0000_0036

/-! Generated from the actual pinned z12direct_5_2_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through37. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 37 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 37 inputClause
def concreteCNF : CNF Nat := indexedCNF 37 inputClause
/-- Input SHA256: b8edc2bb4a17f6bf97e29519f6ef9f02f031033a883c9a9584e019616cc23fb1; LRAT SHA256: 82d352a1cd99035ac546af0bc8c89605ae34ccda79274de00c6d10c97e61cabf. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 37 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_2_9
