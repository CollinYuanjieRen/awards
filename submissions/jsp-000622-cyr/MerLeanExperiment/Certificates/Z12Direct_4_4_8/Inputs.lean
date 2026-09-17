import MerLeanExperiment.Certificates.Z12Direct_4_4_8.Clauses0000_0244

/-! Generated from the actual pinned z12direct_4_4_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through245. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 245 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 245 inputClause
def concreteCNF : CNF Nat := indexedCNF 245 inputClause
/-- Input SHA256: 3a44fd823ab98107b7c9baac613a9d8b542e305713bdbaf730e849c967f27ed5; LRAT SHA256: eaebeee7eea76a72e41a8abbab7f8a4cfa7196b1fc80417bdfcbae7f6d28f803. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 245 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_4_8
