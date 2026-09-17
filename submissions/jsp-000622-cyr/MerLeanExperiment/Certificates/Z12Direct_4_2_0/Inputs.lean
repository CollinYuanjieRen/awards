import MerLeanExperiment.Certificates.Z12Direct_4_2_0.Clauses0000_0094

/-! Generated from the actual pinned z12direct_4_2_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through95. -/
def inputClause (id : Nat) : DefaultClause 29 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 29 → Bool) : Prop :=
  ∀ i, i < 95 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 29 := indexedFormula 95 inputClause
def concreteCNF : CNF Nat := indexedCNF 95 inputClause
/-- Input SHA256: e10185fbcab52796bc498ec601577de62431369cb8f0580e4bdb55945efae654; LRAT SHA256: a503745412c238075c1dd17dd17371b429b8dc867cb11b9038fc8f19278b7346. -/
theorem initialFormula_supplies_inputs (a : PosFin 29 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 95 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_4_2_0
