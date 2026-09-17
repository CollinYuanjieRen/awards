import MerLeanExperiment.Certificates.Z12Direct_5_5_7.Clauses0000_0217

/-! Generated from the actual pinned z12direct_5_5_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through218. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 218 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 218 inputClause
def concreteCNF : CNF Nat := indexedCNF 218 inputClause
/-- Input SHA256: 0f368646dcf3bcac27e8dd94bc2a537805d5497973442357d7696775734b6a97; LRAT SHA256: 527e0c862f0643c89a0ca0ea7ee99612703554e19e085087a7bf415f00b68eb1. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 218 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_7
