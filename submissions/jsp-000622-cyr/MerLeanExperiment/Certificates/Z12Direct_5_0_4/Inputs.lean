import MerLeanExperiment.Certificates.Z12Direct_5_0_4.Clauses0000_0174

/-! Generated from the actual pinned z12direct_5_0_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through175. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 175 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 175 inputClause
def concreteCNF : CNF Nat := indexedCNF 175 inputClause
/-- Input SHA256: 55b43f83fa8c90f4032e898e5e77598ae3675bd7b9bf63bb06f42563a360f698; LRAT SHA256: 6fc7f463a58a0bc99760f4d0c0f4448a33acc36542c6c1b691a913df24e94211. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 175 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_4
