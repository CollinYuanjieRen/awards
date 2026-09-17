import MerLeanExperiment.Certificates.Z12Direct_4_2_7.Clauses0000_0073

/-! Generated from the actual pinned z12direct_4_2_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through74. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 74 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 74 inputClause
def concreteCNF : CNF Nat := indexedCNF 74 inputClause
/-- Input SHA256: dce9d97f2ffacfd42afe51a925898adda04a76572c1ff9e82b5f9267f52ad1fb; LRAT SHA256: 3c75d9f136805519bc7261b197378998f8a468345a24931777359286906e32f3. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 74 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_7
