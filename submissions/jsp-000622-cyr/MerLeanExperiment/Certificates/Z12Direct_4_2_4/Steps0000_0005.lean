import MerLeanExperiment.Certificates.Z12Direct_4_2_4.Inputs

/-! Generated from the actual pinned z12direct_4_2_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c15 : DefaultClause 29 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f15 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c11, some c12, some c4, some c6, some c2, some c1, some c9, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p15 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked15 : lratChecker f15 p15 = .success := by decide +kernel
theorem unsat15 : Unsatisfiable (PosFin 29) f15 := by
  apply lratCheckerSound f15 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p15
  · intro a ha; simp [p15] at ha; subst a; trivial
  · exact checked15
theorem derived15 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c15 := by
  apply localUnsat_implies_entails f15 [c11, c12, c4, c6, c2, c1, c9] c15 unsat15 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c16 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f16 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c3, some c5, some c7, some c2, some c1, some c8, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p16 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked16 : lratChecker f16 p16 = .success := by decide +kernel
theorem unsat16 : Unsatisfiable (PosFin 29) f16 := by
  apply lratCheckerSound f16 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p16
  · intro a ha; simp [p16] at ha; subst a; trivial
  · exact checked16
theorem derived16 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c16 := by
  apply localUnsat_implies_entails f16 [c3, c5, c7, c2, c1, c8] c16 unsat16 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c17 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f17 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c11, some c12, some c15, some c16, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p17 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked17 : lratChecker f17 p17 = .success := by decide +kernel
theorem unsat17 : Unsatisfiable (PosFin 29) f17 := by
  apply lratCheckerSound f17 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p17
  · intro a ha; simp [p17] at ha; subst a; trivial
  · exact checked17
theorem derived17 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c17 := by
  apply localUnsat_implies_entails f17 [c11, c12, c15, c16] c17 unsat17 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c15 := derived15 a h
  have h3 : Entails.eval a c16 := derived16 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c18 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f18 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c17, some c10, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p18 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked18 : lratChecker f18 p18 = .success := by decide +kernel
theorem unsat18 : Unsatisfiable (PosFin 29) f18 := by
  apply lratCheckerSound f18 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p18
  · intro a ha; simp [p18] at ha; subst a; trivial
  · exact checked18
theorem derived18 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c18 := by
  apply localUnsat_implies_entails f18 [c17, c10] c18 unsat18 (by rfl) a
  have h0 : Entails.eval a c17 := derived17 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c19 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f19 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c17, some c13, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p19 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked19 : lratChecker f19 p19 = .success := by decide +kernel
theorem unsat19 : Unsatisfiable (PosFin 29) f19 := by
  apply lratCheckerSound f19 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p19
  · intro a ha; simp [p19] at ha; subst a; trivial
  · exact checked19
theorem derived19 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c19 := by
  apply localUnsat_implies_entails f19 [c17, c13] c19 unsat19 (by rfl) a
  have h0 : Entails.eval a c17 := derived17 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c20 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f20 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c19, some c18, some c14]
def p20 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked20 : lratChecker f20 p20 = .success := by decide +kernel
theorem unsat20 : Unsatisfiable (PosFin 29) f20 := by
  apply lratCheckerSound f20 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p20
  · intro a ha; simp [p20] at ha; subst a; trivial
  · exact checked20
theorem derived20 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c20 := by
  apply localUnsat_implies_entails f20 [c19, c18, c14] c20 unsat20 (by rfl) a
  have h0 : Entails.eval a c19 := derived19 a h
  have h1 : Entails.eval a c18 := derived18 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived20

end CochromaticTwenty.Certificates.Z12Direct_4_2_4
