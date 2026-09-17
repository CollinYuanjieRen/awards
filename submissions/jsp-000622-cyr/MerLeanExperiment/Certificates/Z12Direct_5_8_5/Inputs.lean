import MerLeanExperiment.Certificates.Z12Direct_5_8_5.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_5.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_5.Clauses0500_0527

/-! Generated from the actual pinned z12direct_5_8_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through528. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 528 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 528 inputClause
def concreteCNF : CNF Nat := indexedCNF 528 inputClause
/-- Input SHA256: 079ccab91d65112bb5d0b2eeadf93ffdb550229e24d8232170923253c41da48a; LRAT SHA256: 888645c54cb91a523a2af613cb7e72ac2bb586fd14e8de9728c274df607db8af. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 528 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_5
