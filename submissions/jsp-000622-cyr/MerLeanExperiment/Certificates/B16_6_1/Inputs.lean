import MerLeanExperiment.Certificates.B16_6_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_6_1.Clauses0250_0372

/-! Generated from the actual pinned b16_6_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through373. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 373 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 373 inputClause
def concreteCNF : CNF Nat := indexedCNF 373 inputClause
/-- Input SHA256: 540015efe8f190d6c34563b56b37eaa727f94dc1dfa7b49516dff19d94390c0e; LRAT SHA256: 85527c3370e46804f3319cc012bec7db38efd40adff99cfbbc28ecd0608ba5b5. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 373 inputClause a h

end CochromaticTwenty.Certificates.B16_6_1
