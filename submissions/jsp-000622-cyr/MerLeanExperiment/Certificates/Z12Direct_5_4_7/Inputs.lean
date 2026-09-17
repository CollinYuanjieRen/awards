import MerLeanExperiment.Certificates.Z12Direct_5_4_7.Clauses0000_0240

/-! Generated from the actual pinned z12direct_5_4_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through241. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 241 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 241 inputClause
def concreteCNF : CNF Nat := indexedCNF 241 inputClause
/-- Input SHA256: 56dcb0bc3fb5d1ea5d74a27c3dffede8574082741a1936c45494baec3366a602; LRAT SHA256: c8f51a5ccbd20e1acaccff39abdf321635ef7233dca783438fb36867e8e7285a. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 241 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_7
