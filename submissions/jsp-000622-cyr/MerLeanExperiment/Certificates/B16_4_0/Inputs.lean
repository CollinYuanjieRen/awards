import MerLeanExperiment.Certificates.B16_4_0.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_4_0.Clauses0250_0355

/-! Generated from the actual pinned b16_4_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through356. -/
def inputClause (id : Nat) : DefaultClause 57 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 57 → Bool) : Prop :=
  ∀ i, i < 356 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 57 := indexedFormula 356 inputClause
def concreteCNF : CNF Nat := indexedCNF 356 inputClause
/-- Input SHA256: 49ea997c1fe5a477afee3c7f7afb9350b99d9537374d4864fe42857c4bf3d264; LRAT SHA256: e9271436dd66e576dd171ce4e2bee5677b05c6e7d92eef5025ae8254454baaa4. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 356 inputClause a h

end CochromaticTwenty.Certificates.B16_4_0
