import MerLeanExperiment.Certificates.Z12Direct_4_2_8.Steps0000_0099

/-! Generated from the actual pinned z12direct_4_2_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c298 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f298 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c296, some c297, some c293, some c69, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p298 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked298 : lratChecker f298 p298 = .success := by decide +kernel
theorem unsat298 : Unsatisfiable (PosFin 29) f298 := by
  apply lratCheckerSound f298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p298
  · intro a ha; simp [p298] at ha; subst a; trivial
  · exact checked298
theorem derived298 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c298 := by
  apply localUnsat_implies_entails f298 [c296, c297, c293, c69] c298 unsat298 (by rfl) a
  have h0 : Entails.eval a c296 := derived296 a h
  have h1 : Entails.eval a c297 := derived297 a h
  have h2 : Entails.eval a c293 := derived293 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c299 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c297, some c286, some c293, some c57, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p299 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 29) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c297, c286, c293, c57] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c297 := derived297 a h
  have h1 : Entails.eval a c286 := derived286 a h
  have h2 : Entails.eval a c293 := derived293 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c300 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c299, some c298, some c278, some c285, some c3]
def p300 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 29) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c299, c298, c278, c285, c3] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c298 := derived298 a h
  have h2 : Entails.eval a c278 := derived278 a h
  have h3 : Entails.eval a c285 := derived285 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived300

end CochromaticTwenty.Certificates.Z12Direct_4_2_8
