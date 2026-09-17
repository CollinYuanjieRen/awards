import MerLeanExperiment.Certificates.Z12Direct_5_3_7.Clauses0000_0188

/-! Generated from the actual pinned z12direct_5_3_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through189. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 189 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 189 inputClause
def concreteCNF : CNF Nat := indexedCNF 189 inputClause
/-- Input SHA256: 75c10d57385ac6c06aff7bf7a17cf3060caf0fce3d200e0b7ee3d265786a29bd; LRAT SHA256: 25dbd753617781350c98251e491de5274264daac790edfe42da47ae42cce0ae4. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 189 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_3_7
