import MerLeanExperiment.Certificates.B16_4_1.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_4_1.Clauses0250_0383

/-! Generated from the actual pinned b16_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through384. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 384 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 384 inputClause
def concreteCNF : CNF Nat := indexedCNF 384 inputClause
/-- Input SHA256: b3dbbea59f5dcd27d91098a6bb67920e716aef7bf18450c3a55fea4436d0b94f; LRAT SHA256: ed951a940f80c3764db76123e07b3eaea9d5952f2864f98f01f3f432d1826e90. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 384 inputClause a h

end CochromaticTwenty.Certificates.B16_4_1
