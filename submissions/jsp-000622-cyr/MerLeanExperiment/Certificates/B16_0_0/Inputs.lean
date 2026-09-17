import MerLeanExperiment.Certificates.B16_0_0.Clauses0000_0249
import MerLeanExperiment.Certificates.B16_0_0.Clauses0250_0392

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
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
/-- Input SHA256: dfb3a3b92f4321e44179fa269cc9326702d78db6ea6c689d41fe38519c72f104; LRAT SHA256: 638d8e072c915ad6d9cf73f067a9887d103d7ec4655ccec59930df546cd6deb6. -/
theorem initialFormula_supplies_inputs (a : PosFin 57 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 393 inputClause a h

end CochromaticTwenty.Certificates.B16_0_0
