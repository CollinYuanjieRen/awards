import MerLeanExperiment.Certificates.Z12Direct_5_0_3.Clauses0000_0169

/-! Generated from the actual pinned z12direct_5_0_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through170. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 170 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 170 inputClause
def concreteCNF : CNF Nat := indexedCNF 170 inputClause
/-- Input SHA256: 4e284c4153eb6498d35da78eba15efd484eb9a8dc50f76c61629c3b4c1bc383e; LRAT SHA256: ae30c6f3b86d5c8cc78386fd52c55db79d9d19f27bbcc7d0e174d9b38c029080. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 170 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_0_3
