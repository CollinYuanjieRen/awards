import MerLeanExperiment.Certificates.Z12Direct_5_5_7.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_5_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c319 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f319 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c318, some c308, some c317, some c287, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p319 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked319 : lratChecker f319 p319 = .success := by decide +kernel
theorem unsat319 : Unsatisfiable (PosFin 31) f319 := by
  apply lratCheckerSound f319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p319
  · intro a ha; simp [p319] at ha; subst a; trivial
  · exact checked319
theorem derived319 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c319 := by
  apply localUnsat_implies_entails f319 [c318, c308, c317, c287] c319 unsat319 (by rfl) a
  have h0 : Entails.eval a c318 := derived318 a h
  have h1 : Entails.eval a c308 := derived308 a h
  have h2 : Entails.eval a c317 := derived317 a h
  have h3 : Entails.eval a c287 := derived287 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c320 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f320 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c318, some c319, some c317, some c284, some c131]
def p320 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked320 : lratChecker f320 p320 = .success := by decide +kernel
theorem unsat320 : Unsatisfiable (PosFin 31) f320 := by
  apply lratCheckerSound f320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p320
  · intro a ha; simp [p320] at ha; subst a; trivial
  · exact checked320
theorem derived320 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c320 := by
  apply localUnsat_implies_entails f320 [c318, c319, c317, c284, c131] c320 unsat320 (by rfl) a
  have h0 : Entails.eval a c318 := derived318 a h
  have h1 : Entails.eval a c319 := derived319 a h
  have h2 : Entails.eval a c317 := derived317 a h
  have h3 : Entails.eval a c284 := derived284 a h
  have h4 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived320

end CochromaticTwenty.Certificates.Z12Direct_5_5_7
