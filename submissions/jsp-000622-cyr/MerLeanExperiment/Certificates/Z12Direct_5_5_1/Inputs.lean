import MerLeanExperiment.Certificates.Z12Direct_5_5_1.Clauses0000_0142

/-! Generated from the actual pinned z12direct_5_5_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through143. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 143 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 143 inputClause
def concreteCNF : CNF Nat := indexedCNF 143 inputClause
/-- Input SHA256: cadb79bcf8eef9a00fa60f246c9c2f3f274345713e025a3a5aafbfc8a6d283ee; LRAT SHA256: ac293d2ec052cc2f760b218264dbe8d54bdd9adfe766271f1926122cd89894e2. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 143 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_5_1
