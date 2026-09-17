import MerLeanExperiment.Certificates.B16_1_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_1_2.Clauses0250_0392

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through393. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 393 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 393 inputClause
def concreteCNF : CNF Nat := indexedCNF 393 inputClause
/-- Input SHA256: 27f2a9744948fcc045fff0b3c08630104a0a7eef6e636c21a76f4dda4c55340e; LRAT SHA256: 19f397a75c934325dcece242ff5c7d816276a792f6ecc177641fe10e9dcda4f7. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 393 inputClause a h

end CochromaticTwenty.Certificates.B16_1_2
