import MerLeanExperiment.Certificates.Z12Direct_4_1_0.Clauses0000_0089

/-! Generated from the actual pinned z12direct_4_1_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through90. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 90 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 90 inputClause
def concreteCNF : CNF Nat := indexedCNF 90 inputClause
/-- Input SHA256: 82a938e9d9524c17de767bcef7971c484df8cf225af03cbc21eb5d0c640e1225; LRAT SHA256: f0635116d93c10796f38e079caa963c0866669fd15ad531e97a4519fd57af2dd. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 90 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_1_0
