import MerLeanExperiment.Certificates.Z12Direct_5_7_4.Clauses0000_0124

/-! Generated from the actual pinned z12direct_5_7_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through125. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 125 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 125 inputClause
def concreteCNF : CNF Nat := indexedCNF 125 inputClause
/-- Input SHA256: 8d3fe22a4b8c65f395cb1a2719d6a9643f08e461c38646cc98110c6b5d5c7126; LRAT SHA256: 9285f3fa691ee4d9a477ee22d47b47dbf89a12d60fa0256fd9d4f7b0f5c549df. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 125 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_7_4
