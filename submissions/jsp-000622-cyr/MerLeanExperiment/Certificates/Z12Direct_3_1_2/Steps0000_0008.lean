import MerLeanExperiment.Certificates.Z12Direct_3_1_2.Inputs

/-! Generated from the actual pinned z12direct_3_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_3_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c13 : DefaultClause 9 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f13 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c4, some c7, some c6, some c9, some c11, some c12, some c10, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p13 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked13 : lratChecker f13 p13 = .success := by decide +kernel
theorem unsat13 : Unsatisfiable (PosFin 9) f13 := by
  apply lratCheckerSound f13 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p13
  · intro a ha; simp [p13] at ha; subst a; trivial
  · exact checked13
theorem derived13 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c13 := by
  apply localUnsat_implies_entails f13 [c4, c7, c6, c9, c11, c12, c10] c13 unsat13 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c14 : DefaultClause 9 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f14 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c13, some c1, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p14 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked14 : lratChecker f14 p14 = .success := by decide +kernel
theorem unsat14 : Unsatisfiable (PosFin 9) f14 := by
  apply lratCheckerSound f14 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p14
  · intro a ha; simp [p14] at ha; subst a; trivial
  · exact checked14
theorem derived14 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c14 := by
  apply localUnsat_implies_entails f14 [c13, c1] c14 unsat14 (by rfl) a
  have h0 : Entails.eval a c13 := derived13 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c15 : DefaultClause 9 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f15 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c14, some c2, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p15 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked15 : lratChecker f15 p15 = .success := by decide +kernel
theorem unsat15 : Unsatisfiable (PosFin 9) f15 := by
  apply lratCheckerSound f15 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p15
  · intro a ha; simp [p15] at ha; subst a; trivial
  · exact checked15
theorem derived15 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c15 := by
  apply localUnsat_implies_entails f15 [c14, c2] c15 unsat15 (by rfl) a
  have h0 : Entails.eval a c14 := derived14 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c16 : DefaultClause 9 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f16 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c14, some c3, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p16 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked16 : lratChecker f16 p16 = .success := by decide +kernel
theorem unsat16 : Unsatisfiable (PosFin 9) f16 := by
  apply lratCheckerSound f16 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p16
  · intro a ha; simp [p16] at ha; subst a; trivial
  · exact checked16
theorem derived16 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c16 := by
  apply localUnsat_implies_entails f16 [c14, c3] c16 unsat16 (by rfl) a
  have h0 : Entails.eval a c14 := derived14 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c17 : DefaultClause 9 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f17 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c15, some c6, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p17 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked17 : lratChecker f17 p17 = .success := by decide +kernel
theorem unsat17 : Unsatisfiable (PosFin 9) f17 := by
  apply lratCheckerSound f17 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p17
  · intro a ha; simp [p17] at ha; subst a; trivial
  · exact checked17
theorem derived17 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c17 := by
  apply localUnsat_implies_entails f17 [c15, c6] c17 unsat17 (by rfl) a
  have h0 : Entails.eval a c15 := derived15 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c18 : DefaultClause 9 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f18 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c16, some c9, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p18 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked18 : lratChecker f18 p18 = .success := by decide +kernel
theorem unsat18 : Unsatisfiable (PosFin 9) f18 := by
  apply lratCheckerSound f18 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p18
  · intro a ha; simp [p18] at ha; subst a; trivial
  · exact checked18
theorem derived18 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c18 := by
  apply localUnsat_implies_entails f18 [c16, c9] c18 unsat18 (by rfl) a
  have h0 : Entails.eval a c16 := derived16 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c19 : DefaultClause 9 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f19 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c17, some c5, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p19 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked19 : lratChecker f19 p19 = .success := by decide +kernel
theorem unsat19 : Unsatisfiable (PosFin 9) f19 := by
  apply lratCheckerSound f19 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p19
  · intro a ha; simp [p19] at ha; subst a; trivial
  · exact checked19
theorem derived19 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c19 := by
  apply localUnsat_implies_entails f19 [c17, c5] c19 unsat19 (by rfl) a
  have h0 : Entails.eval a c17 := derived17 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c20 : DefaultClause 9 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f20 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c18, some c8, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p20 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2]]
theorem checked20 : lratChecker f20 p20 = .success := by decide +kernel
theorem unsat20 : Unsatisfiable (PosFin 9) f20 := by
  apply lratCheckerSound f20 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p20
  · intro a ha; simp [p20] at ha; subst a; trivial
  · exact checked20
theorem derived20 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c20 := by
  apply localUnsat_implies_entails f20 [c18, c8] c20 unsat20 (by rfl) a
  have h0 : Entails.eval a c18 := derived18 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c21 : DefaultClause 9 := directClause [] (by decide +kernel) (by decide +kernel)
def f21 : DefaultFormula 9 := DefaultFormula.ofArray #[none, some c20, some c19, some c10]
def p21 : List (Action (DefaultClause 9) (PosFin 9)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked21 : lratChecker f21 p21 = .success := by decide +kernel
theorem unsat21 : Unsatisfiable (PosFin 9) f21 := by
  apply lratCheckerSound f21 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p21
  · intro a ha; simp [p21] at ha; subst a; trivial
  · exact checked21
theorem derived21 (a : PosFin 9 → Bool) (h : InputSat a) : Entails.eval a c21 := by
  apply localUnsat_implies_entails f21 [c20, c19, c10] c21 unsat21 (by rfl) a
  have h0 : Entails.eval a c20 := derived20 a h
  have h1 : Entails.eval a c19 := derived19 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived21

end CochromaticTwenty.Certificates.Z12Direct_3_1_2
