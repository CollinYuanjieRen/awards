import MerLeanExperiment.Certificates.Z12Direct_5_6_5.Clauses0000_0167

/-! Generated from the actual pinned z12direct_5_6_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through168. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 168 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 168 inputClause
def concreteCNF : CNF Nat := indexedCNF 168 inputClause
/-- Input SHA256: 502c9d01bde795e113c21c17e9e23f3c678d44f9818e460a5591bd9057ddaa96; LRAT SHA256: 9044def835fc546eac9de89e2cb81c550b0cdaa0897b53c6b266eaea0b41c082. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 168 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_5
