import MerLeanExperiment.Certificates.Z12Direct_3_1_1.Inputs

/-! Generated from the actual pinned z12direct_3_1_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7 : DefaultClause 9 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c1, some c2, some c4, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p7 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7 : lratChecker f7 p7 = .success := by decide +kernel
theorem unsat7 : Unsatisfiable (PosFin 9) f7 := by
  apply lratCheckerSound f7 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7
  · intro a ha; simp [p7] at ha; subst a; trivial
  · exact checked7
theorem derived7 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c7 := by
  apply localUnsat_implies_entails f7 [c1, c2, c4] c7 unsat7 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8 : DefaultClause 9 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c7, some c3, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p8 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked8 : lratChecker f8 p8 = .success := by decide +kernel
theorem unsat8 : Unsatisfiable (PosFin 9) f8 := by
  apply lratCheckerSound f8 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8
  · intro a ha; simp [p8] at ha; subst a; trivial
  · exact checked8
theorem derived8 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c8 := by
  apply localUnsat_implies_entails f8 [c7, c3] c8 unsat8 (by rfl) a
  have h0 : Entails.eval a c7 := derived7 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9 : DefaultClause 9 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c8, some c5, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p9 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked9 : lratChecker f9 p9 = .success := by decide +kernel
theorem unsat9 : Unsatisfiable (PosFin 9) f9 := by
  apply lratCheckerSound f9 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9
  · intro a ha; simp [p9] at ha; subst a; trivial
  · exact checked9
theorem derived9 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c9 := by
  apply localUnsat_implies_entails f9 [c8, c5] c9 unsat9 (by rfl) a
  have h0 : Entails.eval a c8 := derived8 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c10 : DefaultClause 9 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f10 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c8, some c6, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p10 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked10 : lratChecker f10 p10 = .success := by decide +kernel
theorem unsat10 : Unsatisfiable (PosFin 9) f10 := by
  apply lratCheckerSound f10 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10
  · intro a ha; simp [p10] at ha; subst a; trivial
  · exact checked10
theorem derived10 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c10 := by
  apply localUnsat_implies_entails f10 [c8, c6] c10 unsat10 (by rfl) a
  have h0 : Entails.eval a c8 := derived8 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c11 : DefaultClause 9 := directClause [] (by decide +kernel) (by decide +kernel)
def f11 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c9, some c10, some c4]
def p11 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked11 : lratChecker f11 p11 = .success := by decide +kernel
theorem unsat11 : Unsatisfiable (PosFin 9) f11 := by
  apply lratCheckerSound f11 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11
  · intro a ha; simp [p11] at ha; subst a; trivial
  · exact checked11
theorem derived11 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c11 := by
  apply localUnsat_implies_entails f11 [c9, c10, c4] c11 unsat11 (by rfl) a
  have h0 : Entails.eval a c9 := derived9 a h
  have h1 : Entails.eval a c10 := derived10 a h
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived11

end CochromaticTwenty.Certificates.Z12Direct_3_1_1
