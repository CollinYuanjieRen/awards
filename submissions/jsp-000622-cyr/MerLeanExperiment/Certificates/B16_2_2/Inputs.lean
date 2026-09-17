import MerLeanExperiment.Certificates.B16_2_2.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_2_2.Clauses0250_0382

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
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
/-- Input SHA256: 2c8cc443248ffeffe34627f1054f4ea01e3a24d5419f5a010f51203c78ab4014; LRAT SHA256: 3bcbdf95564c64fe184b497a0e5da5f1b04389f1ab0451404c8570e53aa156cd. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 383 inputClause a h

end CochromaticTwenty.Certificates.B16_2_2
