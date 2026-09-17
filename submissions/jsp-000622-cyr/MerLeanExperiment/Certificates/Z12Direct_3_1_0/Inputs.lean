import MerLeanExperiment.Certificates.Z12Direct_3_1_0.Clauses0000_0008

/-! Generated from the actual pinned z12direct_3_1_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through9. -/
def inputClause (id : Nat) : DefaultClause 9 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 9 → Bool) : Prop :=
  ∀ i, i < 9 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 9 := indexedFormula 9 inputClause
def concreteCNF : CNF Nat := indexedCNF 9 inputClause
/-- Input SHA256: fd6267b9b78b15fffcb69e2567595189eab3dfeb67a98e31c1f2a0f572e9fb1c; LRAT SHA256: f70157dfeda454bb8c1bc4f85eaaccffd879b4efbf584ecf61e381a9b5cf96f2. -/
theorem initialFormula_supplies_inputs (a : PosFin 9 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 9 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_3_1_0
