import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Clauses0250_0499
import MerLeanExperiment.Certificates.Z12Direct_5_8_9.Clauses0500_0556

/-! Generated from the actual pinned z12direct_5_8_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through557. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | 2 => inputBlock2.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 557 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 557 inputClause
def concreteCNF : CNF Nat := indexedCNF 557 inputClause
/-- Input SHA256: f8180e840c92efd26b1ac12d24f745513242c431fd3c01f24abcd2d8d89aa47b; LRAT SHA256: a6f4fc75375d0984451508533de93b0e88549bdb868dd09217ddcdce4922b699. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 557 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_8_9
