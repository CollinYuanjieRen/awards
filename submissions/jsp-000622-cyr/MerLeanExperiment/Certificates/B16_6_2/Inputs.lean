import MerLeanExperiment.Certificates.B16_6_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_6_2.Clauses0250_0391

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through392. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 392 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 392 inputClause
def concreteCNF : CNF Nat := indexedCNF 392 inputClause
/-- Input SHA256: 6009be24d36ca15e923ce89c7c9afbe99f95f9bb37b0c379f3f922604877d82b; LRAT SHA256: 9ef05e131df9b1981008e77d625717a61afce61e78dd5c88dda975a5a49baac9. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 392 inputClause a h

end CochromaticTwenty.Certificates.B16_6_2
