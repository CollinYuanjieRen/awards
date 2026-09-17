import MerLeanExperiment.Certificates.Z12Direct_5_0_10.Clauses0000_0026

/-! Generated from the actual pinned z12direct_5_0_10-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_10
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through27. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 27 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 27 inputClause
def concreteCNF : CNF Nat := indexedCNF 27 inputClause
/-- Input SHA256: 764bf291299cda2ce099dd0483f6777ef72ae36c28cb46dec75c0085f43fd1f9; LRAT SHA256: b2183cedb9af5e0f033eade7e53961067f397c18928005ea35d17429258b26d9. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 27 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_10
