import MerLeanExperiment.Certificates.Z12Direct_5_3_1.Clauses0000_0197

/-! Generated from the actual pinned z12direct_5_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through198. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 198 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 198 inputClause
def concreteCNF : CNF Nat := indexedCNF 198 inputClause
/-- Input SHA256: f8d552f3a40ef14d8392a16277b7c2847eb3631b8af1dca819f38f12bcddfc31; LRAT SHA256: 65e45af2b9437fe513ba31db917e993966b67504b29adad56d89ee6560f449e6. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 198 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_1
