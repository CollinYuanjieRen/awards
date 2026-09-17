import MerLeanExperiment.Certificates.Z12Direct_5_1_7.Inputs

/-! Generated from the actual pinned z12direct_5_1_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2 : DefaultClause 1 := directClause [] (by decide +kernel) (by decide +kernel)
def f2 : DefaultFormula 1 := DefaultFormula.ofArray #[none, some c1]
def p2 : List (Action (DefaultClause 1) (PosFin 1)) := [.addEmpty 0 #[1]]
theorem checked2 : lratChecker f2 p2 = .success := by decide +kernel
theorem unsat2 : Unsatisfiable (PosFin 1) f2 := by
  apply lratCheckerSound f2 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2
  · intro a ha; simp [p2] at ha; subst a; trivial
  · exact checked2
theorem derived2 (a : PosFin 1 → Bool) (h : InputSat a) : Entails.eval a c2 := by
  apply localUnsat_implies_entails f2 [c1] c2 unsat2 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl <;> assumption
#print axioms derived2

end CochromaticTwenty.Certificates.Z12Direct_5_1_7
