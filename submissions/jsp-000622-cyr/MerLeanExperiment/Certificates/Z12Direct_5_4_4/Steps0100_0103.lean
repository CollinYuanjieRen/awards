import MerLeanExperiment.Certificates.Z12Direct_5_4_4.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_4_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c300 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c266, some c295, some c106, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked300 : lratChecker f300 p300 = .success := by decide +kernel
theorem unsat300 : Unsatisfiable (PosFin 31) f300 := by
  apply lratCheckerSound f300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p300
  · intro a ha; simp [p300] at ha; subst a; trivial
  · exact checked300
theorem derived300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c300 := by
  apply localUnsat_implies_entails f300 [c299, c266, c295, c106] c300 unsat300 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c266 := derived266 a h
  have h2 : Entails.eval a c295 := derived295 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c301 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c295, some c266, some c107, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked301 : lratChecker f301 p301 = .success := by decide +kernel
theorem unsat301 : Unsatisfiable (PosFin 31) f301 := by
  apply lratCheckerSound f301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p301
  · intro a ha; simp [p301] at ha; subst a; trivial
  · exact checked301
theorem derived301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c301 := by
  apply localUnsat_implies_entails f301 [c299, c295, c266, c107] c301 unsat301 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c295 := derived295 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c302 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c299, some c295, some c283, some c90, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked302 : lratChecker f302 p302 = .success := by decide +kernel
theorem unsat302 : Unsatisfiable (PosFin 31) f302 := by
  apply lratCheckerSound f302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p302
  · intro a ha; simp [p302] at ha; subst a; trivial
  · exact checked302
theorem derived302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c302 := by
  apply localUnsat_implies_entails f302 [c299, c295, c283, c90] c302 unsat302 (by rfl) a
  have h0 : Entails.eval a c299 := derived299 a h
  have h1 : Entails.eval a c295 := derived295 a h
  have h2 : Entails.eval a c283 := derived283 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c303 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c300, some c301, some c302, some c298, some c5]
def p303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked303 : lratChecker f303 p303 = .success := by decide +kernel
theorem unsat303 : Unsatisfiable (PosFin 31) f303 := by
  apply lratCheckerSound f303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p303
  · intro a ha; simp [p303] at ha; subst a; trivial
  · exact checked303
theorem derived303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c303 := by
  apply localUnsat_implies_entails f303 [c300, c301, c302, c298, c5] c303 unsat303 (by rfl) a
  have h0 : Entails.eval a c300 := derived300 a h
  have h1 : Entails.eval a c301 := derived301 a h
  have h2 : Entails.eval a c302 := derived302 a h
  have h3 : Entails.eval a c298 := derived298 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived303

end CochromaticTwenty.Certificates.Z12Direct_5_4_4
