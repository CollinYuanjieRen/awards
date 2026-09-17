import MerLeanExperiment.Certificates.Z12Direct_5_5_8.Clauses0000_0194

/-! Generated from the actual pinned z12direct_5_5_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through195. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 195 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 195 inputClause
def concreteCNF : CNF Nat := indexedCNF 195 inputClause
/-- Input SHA256: 1851418f81b9cef5f53d1337d9ef3fa0040d10afe5182ef3c9b112c2dac1e956; LRAT SHA256: 19073718a2135d5a907b60f0da1737d97eefc685a1e1237acc28785569950478. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 195 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_8
