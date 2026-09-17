import MerLeanExperiment.Certificates.B16_0_2Enumerating.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_0_2Enumerating.Clauses0250_0412

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through413. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 413 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 413 inputClause
def concreteCNF : CNF Nat := indexedCNF 413 inputClause
/-- Input SHA256: 5f77cb23b1f260eb9b41f178103224a404b221cda2d20f88aeed84f774c5916e; LRAT SHA256: e35ad1ec0447bd451d157d496ae1067690476f46264f3f60a6126f380e595656. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 413 inputClause a h

end CochromaticTwenty.Certificates.B16_0_2Enumerating
