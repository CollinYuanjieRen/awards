import MerLeanExperiment.Certificates.Z12Direct_5_4_11.Clauses0000_0249
import MerLeanExperiment.Certificates.Z12Direct_5_4_11.Clauses0250_0272

/-! Generated from the actual pinned z12direct_5_4_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through273. -/
def inputClause (id : Nat) : DefaultClause 31 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | 1 => inputBlock1.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 31 → Bool) : Prop :=
  ∀ i, i < 273 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 31 := indexedFormula 273 inputClause
def concreteCNF : CNF Nat := indexedCNF 273 inputClause
/-- Input SHA256: cc6340e61125d46ef72bd3c011c7d0f6bbf5a438f046b708ad41f544e3eb2d06; LRAT SHA256: c1a278f21f7643940a4933abf16a0c82542bd1d1a13eb4feff8d81b1d8826f19. -/
theorem initialFormula_supplies_inputs (a : PosFin 31 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 273 inputClause a h

end CochromaticTwenty.Certificates.Z12Direct_5_4_11
