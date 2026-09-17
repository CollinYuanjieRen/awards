import MerLeanExperiment.Certificates.Z12Direct_4_0_4.Inputs

/-! Generated from the actual pinned z12direct_4_0_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c12 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f12 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c1, some c5, some c7, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p12 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked12 : lratChecker f12 p12 = .success := by decide +kernel
theorem unsat12 : Unsatisfiable (PosFin 29) f12 := by
  apply lratCheckerSound f12 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p12
  · intro a ha; simp [p12] at ha; subst a; trivial
  · exact checked12
theorem derived12 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c12 := by
  apply localUnsat_implies_entails f12 [c1, c5, c7] c12 unsat12 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c13 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f13 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c4, some c9, some c11, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p13 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked13 : lratChecker f13 p13 = .success := by decide +kernel
theorem unsat13 : Unsatisfiable (PosFin 29) f13 := by
  apply lratCheckerSound f13 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p13
  · intro a ha; simp [p13] at ha; subst a; trivial
  · exact checked13
theorem derived13 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c13 := by
  apply localUnsat_implies_entails f13 [c4, c9, c11] c13 unsat13 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c14 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f14 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c13, some c3, some c12, some c6, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p14 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked14 : lratChecker f14 p14 = .success := by decide +kernel
theorem unsat14 : Unsatisfiable (PosFin 29) f14 := by
  apply lratCheckerSound f14 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p14
  · intro a ha; simp [p14] at ha; subst a; trivial
  · exact checked14
theorem derived14 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c14 := by
  apply localUnsat_implies_entails f14 [c13, c3, c12, c6] c14 unsat14 (by rfl) a
  have h0 : Entails.eval a c13 := derived13 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c12 := derived12 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c15 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f15 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c14, some c2, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p15 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked15 : lratChecker f15 p15 = .success := by decide +kernel
theorem unsat15 : Unsatisfiable (PosFin 29) f15 := by
  apply lratCheckerSound f15 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p15
  · intro a ha; simp [p15] at ha; subst a; trivial
  · exact checked15
theorem derived15 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c15 := by
  apply localUnsat_implies_entails f15 [c14, c2] c15 unsat15 (by rfl) a
  have h0 : Entails.eval a c14 := derived14 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c16 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f16 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c14, some c8, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p16 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked16 : lratChecker f16 p16 = .success := by decide +kernel
theorem unsat16 : Unsatisfiable (PosFin 29) f16 := by
  apply lratCheckerSound f16 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p16
  · intro a ha; simp [p16] at ha; subst a; trivial
  · exact checked16
theorem derived16 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c16 := by
  apply localUnsat_implies_entails f16 [c14, c8] c16 unsat16 (by rfl) a
  have h0 : Entails.eval a c14 := derived14 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c17 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f17 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c16, some c15, some c10]
def p17 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked17 : lratChecker f17 p17 = .success := by decide +kernel
theorem unsat17 : Unsatisfiable (PosFin 29) f17 := by
  apply lratCheckerSound f17 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p17
  · intro a ha; simp [p17] at ha; subst a; trivial
  · exact checked17
theorem derived17 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c17 := by
  apply localUnsat_implies_entails f17 [c16, c15, c10] c17 unsat17 (by rfl) a
  have h0 : Entails.eval a c16 := derived16 a h
  have h1 : Entails.eval a c15 := derived15 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived17

end CochromaticTwenty.Certificates.Z12Direct_4_0_4
