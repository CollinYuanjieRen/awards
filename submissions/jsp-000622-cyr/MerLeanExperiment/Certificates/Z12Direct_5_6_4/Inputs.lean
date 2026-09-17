import MerLeanExperiment.Certificates.Z12Direct_5_6_4.Clauses0000_0122

/-! Generated from the actual pinned z12direct_5_6_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through123. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 123 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 123 inputClause
def concreteCNF : CNF Nat := indexedCNF 123 inputClause
/-- Input SHA256: 61ed2b1b16d3c60014ba3baa284cae672fbfa04149f02aa296b495fa54db74ce; LRAT SHA256: 04b77a541228e14620f785a5ee8019ef55c4aefaf2c8c92ed61c8f80596aed8c. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 123 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_6_4
