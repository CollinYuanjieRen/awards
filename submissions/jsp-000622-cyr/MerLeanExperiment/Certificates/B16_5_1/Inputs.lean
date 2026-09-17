import MerLeanExperiment.Certificates.B16_5_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_5_1.Clauses0250_0335

/-! Generated from the actual pinned b16_5_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_5_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through336. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 336 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 336 inputClause
def concreteCNF : CNF Nat := indexedCNF 336 inputClause
/-- Input SHA256: 9e60e143af6d86abe7315671a4f3fe4df121d7cdbfac42019d1904e691a7908a; LRAT SHA256: 839d1862676d102ca21d6929504fe7dbb4372c24844b320f66ea9e8108fc7138. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 336 inputClause a h

end CochromaticTwenty.Certificates.B16_5_1
