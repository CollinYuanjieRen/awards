import MerLeanExperiment.Certificates.Z12Direct_5_4_13.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_4_13.Clauses0250_0361

/-! Generated from the actual pinned z12direct_5_4_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through362. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 362 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 362 inputClause
def concreteCNF : CNF Nat := indexedCNF 362 inputClause
/-- Input SHA256: f3d2c80c5c76c0c1488077b49eb549577d437a844bd0e6b001a58108b9ba8abc; LRAT SHA256: cd3be551ce0e0755c7fb55400414927ee6b81f9ba559af9d7912c3c2c17fd0f9. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 362 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_13
