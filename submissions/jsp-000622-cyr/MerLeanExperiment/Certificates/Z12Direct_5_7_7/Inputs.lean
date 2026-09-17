import MerLeanExperiment.Certificates.Z12Direct_5_7_7.Clauses0000_0221

/-! Generated from the actual pinned z12direct_5_7_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through222. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 222 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 222 inputClause
def concreteCNF : CNF Nat := indexedCNF 222 inputClause
/-- Input SHA256: 4dc1d40edd08772827cd7224721fee3ccca8de78cd5c45c90d113b7fde2aebae; LRAT SHA256: 9f8c43aa2c09d9f7aabe123f4e138db12a075749530427c8788c1a5c23a02247. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 222 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_7
