import MerLeanExperiment.Certificates.Z12Direct_3_1_0.Inputs

/-! Generated from the actual pinned z12direct_3_1_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c10 : DefaultClause 9 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f10 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c2, some c8, some c1, some c9, some c5, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p10 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked10 : lratChecker f10 p10 = .success := by decide +kernel
theorem unsat10 : Unsatisfiable (PosFin 9) f10 := by
  apply lratCheckerSound f10 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p10
  · intro a ha; simp [p10] at ha; subst a; trivial
  · exact checked10
theorem derived10 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c10 := by
  apply localUnsat_implies_entails f10 [c2, c8, c1, c9, c5] c10 unsat10 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c11 : DefaultClause 9 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f11 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c10, some c6, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p11 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked11 : lratChecker f11 p11 = .success := by decide +kernel
theorem unsat11 : Unsatisfiable (PosFin 9) f11 := by
  apply lratCheckerSound f11 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p11
  · intro a ha; simp [p11] at ha; subst a; trivial
  · exact checked11
theorem derived11 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c11 := by
  apply localUnsat_implies_entails f11 [c10, c6] c11 unsat11 (by rfl) a
  have h0 : Entails.eval a c10 := derived10 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c12 : DefaultClause 9 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f12 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c11, some c4, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p12 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked12 : lratChecker f12 p12 = .success := by decide +kernel
theorem unsat12 : Unsatisfiable (PosFin 9) f12 := by
  apply lratCheckerSound f12 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p12
  · intro a ha; simp [p12] at ha; subst a; trivial
  · exact checked12
theorem derived12 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c12 := by
  apply localUnsat_implies_entails f12 [c11, c4] c12 unsat12 (by rfl) a
  have h0 : Entails.eval a c11 := derived11 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c13 : DefaultClause 9 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f13 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c11, some c7, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p13 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked13 : lratChecker f13 p13 = .success := by decide +kernel
theorem unsat13 : Unsatisfiable (PosFin 9) f13 := by
  apply lratCheckerSound f13 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p13
  · intro a ha; simp [p13] at ha; subst a; trivial
  · exact checked13
theorem derived13 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c13 := by
  apply localUnsat_implies_entails f13 [c11, c7] c13 unsat13 (by rfl) a
  have h0 : Entails.eval a c11 := derived11 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c14 : DefaultClause 9 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f14 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c12, some c1, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p14 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked14 : lratChecker f14 p14 = .success := by decide +kernel
theorem unsat14 : Unsatisfiable (PosFin 9) f14 := by
  apply lratCheckerSound f14 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p14
  · intro a ha; simp [p14] at ha; subst a; trivial
  · exact checked14
theorem derived14 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c14 := by
  apply localUnsat_implies_entails f14 [c12, c1] c14 unsat14 (by rfl) a
  have h0 : Entails.eval a c12 := derived12 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c15 : DefaultClause 9 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f15 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c13, some c9, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p15 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked15 : lratChecker f15 p15 = .success := by decide +kernel
theorem unsat15 : Unsatisfiable (PosFin 9) f15 := by
  apply lratCheckerSound f15 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p15
  · intro a ha; simp [p15] at ha; subst a; trivial
  · exact checked15
theorem derived15 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c15 := by
  apply localUnsat_implies_entails f15 [c13, c9] c15 unsat15 (by rfl) a
  have h0 : Entails.eval a c13 := derived13 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c16 : DefaultClause 9 := directClause [] (by decide +kernel) (by decide +kernel)
def f16 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c14, some c15, some c3]
def p16 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked16 : lratChecker f16 p16 = .success := by decide +kernel
theorem unsat16 : Unsatisfiable (PosFin 9) f16 := by
  apply lratCheckerSound f16 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p16
  · intro a ha; simp [p16] at ha; subst a; trivial
  · exact checked16
theorem derived16 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c16 := by
  apply localUnsat_implies_entails f16 [c14, c15, c3] c16 unsat16 (by rfl) a
  have h0 : Entails.eval a c14 := derived14 a h
  have h1 : Entails.eval a c15 := derived15 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived16

end CochromaticTwenty.Certificates.Z12Direct_3_1_0
