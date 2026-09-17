import MerLeanExperiment.Certificates.B16_4_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_4_2.Clauses0250_0382

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through383. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 383 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 383 inputClause
def concreteCNF : CNF Nat := indexedCNF 383 inputClause
/-- Input SHA256: db1d7671c8fa34ffe9bd34d5420e4f0004c3abea5e465ba515379140e9f20cf8; LRAT SHA256: 37abf6fe28e91bab99e37d57c89695dd3c2164f74d0788cf0e9c7c662dacbdc9. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 383 inputClause a h

end CochromaticTwenty.Certificates.B16_4_2
