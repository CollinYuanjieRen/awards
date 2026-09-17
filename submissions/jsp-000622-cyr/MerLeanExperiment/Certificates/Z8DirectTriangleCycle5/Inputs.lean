import MerLeanExperiment.Certificates.Z8DirectTriangleCycle5.Clauses0000_0082

/-! Generated from the actual pinned z8direct_triangle_cycle5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z8DirectTriangleCycle5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-- Concrete DIMACS initial clause lookup, IDs1 through83. -/
def inputClause (id : Nat) : DefaultClause 16 :=
  match (id - 1) / 250 with
  | 0 => inputBlock0.getD ((id - 1) % 250) DefaultClause.empty
  | _ => DefaultClause.empty
def InputSat (a : PosFin 16 → Bool) : Prop :=
  ∀ i, i < 83 → Entails.eval a (inputClause (i + 1))
def initialFormula : DefaultFormula 16 := indexedFormula 83 inputClause
def concreteCNF : CNF Nat := indexedCNF 83 inputClause
/-- Input SHA256: e77d3d88b5b078983e5247d333d7b6b2d60cbbcb3b93e5588db022ba343105d0; LRAT SHA256: 7fe4ed8c94949ed2a343d8aa90873da3b0b3b5c4874b41e2ca20af62edda190b. -/
theorem initialFormula_supplies_inputs (a : PosFin 16 → Bool)
    (h : Entails.eval a initialFormula) : InputSat a :=
  indexedFormula_sat 83 inputClause a h

end CochromaticTwenty.Certificates.Z8DirectTriangleCycle5
