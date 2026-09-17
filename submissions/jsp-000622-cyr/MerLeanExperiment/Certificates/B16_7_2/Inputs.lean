import MerLeanExperiment.Certificates.B16_7_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_7_2.Clauses0250_0387

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through388. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 388 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 388 inputClause
def concreteCNF : CNF Nat := indexedCNF 388 inputClause
/-- Input SHA256: 775ffb1cfb0b39cac72b58ab4179faae928c4b49d389fb8d89ee417d5693cebb; LRAT SHA256: d815e862af5f04e73be42e5bf0b8db3d63b751d7f2d76945e2f9ffa614468ebf. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 388 inputClause a h

end CochromaticTwenty.Certificates.B16_7_2
