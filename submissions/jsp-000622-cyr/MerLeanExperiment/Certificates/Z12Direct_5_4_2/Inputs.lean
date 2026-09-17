import MerLeanExperiment.Certificates.Z12Direct_5_4_2.Clauses0000_0109

/-! Generated from the actual pinned z12direct_5_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through110. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 110 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 110 inputClause
def concreteCNF : CNF Nat := indexedCNF 110 inputClause
/-- Input SHA256: 1a26313221c72fa8f65ca71348f46af9f27884993d38ac1577c8e4b481b3d806; LRAT SHA256: 30aca815c4c39ef42e96866b2158c507acff0cf9fd3f5e6099c5717d7dfa4a07. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 110 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_2
