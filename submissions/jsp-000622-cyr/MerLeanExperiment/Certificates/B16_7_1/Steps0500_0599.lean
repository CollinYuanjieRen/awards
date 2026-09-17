import MerLeanExperiment.Certificates.B16_7_1.Steps0400_0499

/-! Generated from the actual pinned b16_7_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c858 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c650, some c292, some c300, some c651, some c352, some c351, some c170, some c286, some c280, some c179, some c97, some c853, some c131, some c221, some c107, some c298, some c295, some c826, some c191, some c241, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c783, c841, c857, c126, c650, c292, c300, c651, c352, c351, c170, c286, c280, c179, c97, c853, c131, c221, c107, c298, c295, c826, c191, c241] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c651 := derived651 a h
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c351 := h 350 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c97 := h 96 (by decide)
  have h15 : Entails.eval a c853 := derived853 a h
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  have h21 : Entails.eval a c826 := derived826 a h
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c49, some c1, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c99, c49, c1] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c650, some c859, some c295, some c138, some c180, some c107, some c315, some c263, some c150, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c783, c650, c859, c295, c138, c180, c107, c315, c263, c150] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c650 := derived650 a h
  have h2 : Entails.eval a c859 := derived859 a h
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c650, some c300, some c292, some c858, some c184, some c170, some c346, some c352, some c123, some c280, some c37, some c279, some c3, some c297, some c860, some c232, some c231, some c118, some c188, some c193, some c241, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c783, c841, c857, c126, c650, c300, c292, c858, c184, c170, c346, c352, c123, c280, c37, c279, c3, c297, c860, c232, c231, c118, c188, c193, c241] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c858 := derived858 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c352 := h 351 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c297 := h 296 (by decide)
  have h18 : Entails.eval a c860 := derived860 a h
  have h19 : Entails.eval a c232 := h 231 (by decide)
  have h20 : Entails.eval a c231 := h 230 (by decide)
  have h21 : Entails.eval a c118 := h 117 (by decide)
  have h22 : Entails.eval a c188 := h 187 (by decide)
  have h23 : Entails.eval a c193 := h 192 (by decide)
  have h24 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨39, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c857, some c861, some c176, some c841, some c179, some c170, some c315, some c144, some c126, some c720, some c3, some c5, some c265, some c42, some c68, some c320, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c783, c857, c861, c176, c841, c179, c170, c315, c144, c126, c720, c3, c5, c265, c42, c68, c320] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c861 := derived861 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c720 := derived720 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c857, some c861, some c176, some c841, some c179, some c170, some c232, some c111, some c315, some c144, some c103, some c118, some c832, some c249, some c242, some c810, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c783, c857, c861, c176, c841, c179, c170, c232, c111, c315, c144, c103, c118, c832, c249, c242, c810] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c861 := derived861 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c832 := derived832 a h
  have h14 : Entails.eval a c249 := h 248 (by decide)
  have h15 : Entails.eval a c242 := h 241 (by decide)
  have h16 : Entails.eval a c810 := derived810 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c179, some c170, some c352, some c346, some c126, some c232, some c111, some c863, some c37, some c279, some c862, some c297, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c783, c841, c857, c179, c170, c352, c346, c126, c232, c111, c863, c37, c279, c862, c297] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c863 := derived863 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c862 := derived862 a h
  have h14 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c179, some c841, some c857, some c170, some c861, some c176, some c864, some c107, some c315, some c111, some c146, some c126, some c720, some c3, some c5, some c265, some c69, some c62, some c68, some c22, some c154, some c323, some c197, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c783, c179, c841, c857, c170, c861, c176, c864, c107, c315, c111, c146, c126, c720, c3, c5, c265, c69, c62, c68, c22, c154, c323, c197] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c857 := derived857 a h
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c861 := derived861 a h
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c864 := derived864 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c720 := derived720 a h
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c265 := h 264 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c22 := h 21 (by decide)
  have h21 : Entails.eval a c154 := h 153 (by decide)
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c861, some c841, some c857, some c126, some c179, some c176, some c170, some c346, some c864, some c107, some c99, some c116, some c315, some c111, some c865, some c37, some c830, some c704, some c291, some c745, some c238, some c250, some c195, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c783, c861, c841, c857, c126, c179, c176, c170, c346, c864, c107, c99, c116, c315, c111, c865, c37, c830, c704, c291, c745, c238, c250, c195] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c861 := derived861 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c857 := derived857 a h
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c864 := derived864 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c865 := derived865 a h
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c830 := derived830 a h
  have h18 : Entails.eval a c704 := derived704 a h
  have h19 : Entails.eval a c291 := h 290 (by decide)
  have h20 : Entails.eval a c745 := derived745 a h
  have h21 : Entails.eval a c238 := h 237 (by decide)
  have h22 : Entails.eval a c250 := h 249 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c291, some c292, some c655, some c646, some c866, some c443, some c352, some c238, some c654, some c75, some c191, some c195, some c296, some c9, some c745, some c35, some c51, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c783, c841, c857, c126, c291, c292, c655, c646, c866, c443, c352, c238, c654, c75, c191, c195, c296, c9, c745, c35, c51] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c655 := derived655 a h
  have h7 : Entails.eval a c646 := derived646 a h
  have h8 : Entails.eval a c866 := derived866 a h
  have h9 : Entails.eval a c443 := derived443 a h
  have h10 : Entails.eval a c352 := h 351 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c654 := derived654 a h
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c745 := derived745 a h
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c857, some c126, some c291, some c292, some c866, some c867, some c170, some c656, some c184, some c289, some c621, some c191, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c841, c857, c126, c291, c292, c866, c867, c170, c656, c184, c289, c621, c191] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c866 := derived866 a h
  have h6 : Entails.eval a c867 := derived867 a h
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c656 := derived656 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c621 := derived621 a h
  have h12 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c866, some c857, some c841, some c868, some c232, some c239, some c245, some c170, some c113, some c184, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c783, c866, c857, c841, c868, c232, c239, c245, c170, c113, c184] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c868 := derived868 a h
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c239 := h 238 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c866, some c861, some c165, some c835, some c351, some c17, some c76, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c783, c866, c861, c165, c835, c351, c17, c76] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c861 := derived861 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c835 := derived835 a h
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c291, some c292, some c655, some c646, some c866, some c869, some c870, some c184, some c170, some c118, some c111, some c103, some c352, some c315, some c320, some c254, some c654, some c75, some c105, some c296, some c412, some c241, some c193, some c231, some c209, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c783, c841, c857, c126, c291, c292, c655, c646, c866, c869, c870, c184, c170, c118, c111, c103, c352, c315, c320, c254, c654, c75, c105, c296, c412, c241, c193, c231, c209] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c655 := derived655 a h
  have h7 : Entails.eval a c646 := derived646 a h
  have h8 : Entails.eval a c866 := derived866 a h
  have h9 : Entails.eval a c869 := derived869 a h
  have h10 : Entails.eval a c870 := derived870 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c352 := h 351 (by decide)
  have h17 : Entails.eval a c315 := h 314 (by decide)
  have h18 : Entails.eval a c320 := h 319 (by decide)
  have h19 : Entails.eval a c254 := h 253 (by decide)
  have h20 : Entails.eval a c654 := derived654 a h
  have h21 : Entails.eval a c75 := h 74 (by decide)
  have h22 : Entails.eval a c105 := h 104 (by decide)
  have h23 : Entails.eval a c296 := h 295 (by decide)
  have h24 : Entails.eval a c412 := derived412 a h
  have h25 : Entails.eval a c241 := h 240 (by decide)
  have h26 : Entails.eval a c193 := h 192 (by decide)
  have h27 : Entails.eval a c231 := h 230 (by decide)
  have h28 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c857, some c126, some c291, some c292, some c655, some c866, some c435, some c372, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c841, c857, c126, c291, c292, c655, c866, c435, c372] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c866 := derived866 a h
  have h7 : Entails.eval a c435 := derived435 a h
  have h8 : Entails.eval a c372 := derived372 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c292, some c646, some c86, some c88, some c866, some c170, some c872, some c23, some c105, some c252, some c146, some c65, some c315, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c783, c841, c857, c126, c292, c646, c86, c88, c866, c170, c872, c23, c105, c252, c146, c65, c315] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c646 := derived646 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c866 := derived866 a h
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c872 := derived872 a h
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c292, some c646, some c291, some c866, some c88, some c86, some c873, some c184, some c443, some c656, some c80, some c289, some c18, some c49, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c783, c841, c857, c126, c292, c646, c291, c866, c88, c86, c873, c184, c443, c656, c80, c289, c18, c49] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c646 := derived646 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c866 := derived866 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c873 := derived873 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c443 := derived443 a h
  have h13 : Entails.eval a c656 := derived656 a h
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c874, some c871, some c346, some c170, some c126, some c292, some c656, some c289, some c291, some c49, some c18, some c307, some c252, some c254, some c57, some c144, some c61, some c160, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c783, c841, c857, c874, c871, c346, c170, c126, c292, c656, c289, c291, c49, c18, c307, c252, c254, c57, c144, c61, c160] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c874 := derived874 a h
  have h4 : Entails.eval a c871 := derived871 a h
  have h5 : Entails.eval a c346 := h 345 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c254 := h 253 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c61 := h 60 (by decide)
  have h20 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c292, some c874, some c871, some c346, some c656, some c289, some c170, some c646, some c291, some c866, some c49, some c18, some c80, some c96, some c82, some c875, some c105, some c55, some c64, some c221, some c332, some c314, some c199, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c783, c841, c857, c126, c292, c874, c871, c346, c656, c289, c170, c646, c291, c866, c49, c18, c80, c96, c82, c875, c105, c55, c64, c221, c332, c314, c199] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c874 := derived874 a h
  have h6 : Entails.eval a c871 := derived871 a h
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c656 := derived656 a h
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c646 := derived646 a h
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c866 := derived866 a h
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  have h19 : Entails.eval a c875 := derived875 a h
  have h20 : Entails.eval a c105 := h 104 (by decide)
  have h21 : Entails.eval a c55 := h 54 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c221 := h 220 (by decide)
  have h24 : Entails.eval a c332 := h 331 (by decide)
  have h25 : Entails.eval a c314 := h 313 (by decide)
  have h26 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c866, some c841, some c857, some c126, some c292, some c874, some c871, some c346, some c656, some c289, some c876, some c675, some c99, some c221, some c105, some c307, some c252, some c144, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c783, c866, c841, c857, c126, c292, c874, c871, c346, c656, c289, c876, c675, c99, c221, c105, c307, c252, c144] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c866 := derived866 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c857 := derived857 a h
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c874 := derived874 a h
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c876 := derived876 a h
  have h12 : Entails.eval a c675 := derived675 a h
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c841, some c857, some c126, some c861, some c866, some c877, some c97, some c123, some c221, some c346, some c170, some c184, some c131, some c296, some c676, some c99, some c107, some c307, some c256, some c141, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c783, c841, c857, c126, c861, c866, c877, c97, c123, c221, c346, c170, c184, c131, c296, c676, c99, c107, c307, c256, c141] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c857 := derived857 a h
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c861 := derived861 a h
  have h5 : Entails.eval a c866 := derived866 a h
  have h6 : Entails.eval a c877 := derived877 a h
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c676 := derived676 a h
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c107 := h 106 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  have h19 : Entails.eval a c256 := h 255 (by decide)
  have h20 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c63, some c256, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c45, c63, c256] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c91, some c90, some c82, some c64, some c314, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c783, c91, c90, c82, c64, c314] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c123, some c307, some c346, some c97, some c221, some c880, some c63, some c879, some c326, some c99, some c64, some c142, some c11, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c783, c123, c307, c346, c97, c221, c880, c63, c879, c326, c99, c64, c142, c11] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c880 := derived880 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c879 := derived879 a h
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c142 := h 141 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c85, some c649, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c86, c85, c649] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c649 := derived649 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨3, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c882, some c649, some c95, some c71, some c82, some c335, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c783, c882, c649, c95, c71, c82, c335] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c882 := derived882 a h
  have h2 : Entails.eval a c649 := derived649 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c123, some c346, some c97, some c221, some c882, some c881, some c107, some c199, some c332, some c883, some c12, some c91, some c653, some c70, some c13, some c334, some c647, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c783, c123, c346, c97, c221, c882, c881, c107, c199, c332, c883, c12, c91, c653, c70, c13, c334, c647] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c346 := h 345 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c882 := derived882 a h
  have h6 : Entails.eval a c881 := derived881 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c332 := h 331 (by decide)
  have h10 : Entails.eval a c883 := derived883 a h
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c653 := derived653 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c647 := derived647 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c70, some c647, some c334, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c783, c70, c647, c334] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c57, some c332, some c55, some c885, some c94, some c66, some c648, some c309, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c783, c57, c332, c55, c885, c94, c66, c648, c309] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c332 := h 331 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c885 := derived885 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c648 := derived648 a h
  have h8 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c886, some c57, some c332, some c55, some c221, some c107, some c94, some c66, some c323, some c309, some c208, some c65, some c652, some c242, some c96, some c25, some c161, some c215, some c71, some c342, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c783, c878, c886, c57, c332, c55, c221, c107, c94, c66, c323, c309, c208, c65, c652, c242, c96, c25, c161, c215, c71, c342] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c886 := derived886 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c652 := derived652 a h
  have h15 : Entails.eval a c242 := h 241 (by decide)
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c215 := h 214 (by decide)
  have h20 : Entails.eval a c71 := h 70 (by decide)
  have h21 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c57, some c332, some c221, some c107, some c886, some c887, some c45, some c70, some c334, some c342, some c155, some c272, some c71, some c651, some c96, some c676, some c48, some c296, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c783, c57, c332, c221, c107, c886, c887, c45, c70, c334, c342, c155, c272, c71, c651, c96, c676, c48, c296] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c332 := h 331 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c886 := derived886 a h
  have h6 : Entails.eval a c887 := derived887 a h
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c334 := h 333 (by decide)
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c651 := derived651 a h
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c676 := derived676 a h
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c102, some c128, some c223, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c878, c102, c128, c223] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨35, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c123, some c884, some c57, some c332, some c97, some c221, some c107, some c889, some c346, some c888, some c43, some c298, some c593, some c131, some c45, some c653, some c559, some c676, some c351, some c335, some c654, some c71, some c300, some c299, some c92, some c48, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c783, c123, c884, c57, c332, c97, c221, c107, c889, c346, c888, c43, c298, c593, c131, c45, c653, c559, c676, c351, c335, c654, c71, c300, c299, c92, c48] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c884 := derived884 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c332 := h 331 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c889 := derived889 a h
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c888 := derived888 a h
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c593 := derived593 a h
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c653 := derived653 a h
  have h17 : Entails.eval a c559 := derived559 a h
  have h18 : Entails.eval a c676 := derived676 a h
  have h19 : Entails.eval a c351 := h 350 (by decide)
  have h20 : Entails.eval a c335 := h 334 (by decide)
  have h21 : Entails.eval a c654 := derived654 a h
  have h22 : Entails.eval a c71 := h 70 (by decide)
  have h23 : Entails.eval a c300 := h 299 (by decide)
  have h24 : Entails.eval a c299 := h 298 (by decide)
  have h25 : Entails.eval a c92 := h 91 (by decide)
  have h26 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨35, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c890, some c123, some c97, some c221, some c107, some c884, some c346, some c593, some c131, some c653, some c559, some c676, some c351, some c654, some c300, some c299, some c48, some c190, some c20, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c783, c890, c123, c97, c221, c107, c884, c346, c593, c131, c653, c559, c676, c351, c654, c300, c299, c48, c190, c20] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c890 := derived890 a h
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c884 := derived884 a h
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c593 := derived593 a h
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c653 := derived653 a h
  have h11 : Entails.eval a c559 := derived559 a h
  have h12 : Entails.eval a c676 := derived676 a h
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c654 := derived654 a h
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c97, some c123, some c889, some c346, some c890, some c891, some c298, some c297, some c43, some c284, some c22, some c222, some c192, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c783, c97, c123, c889, c346, c890, c891, c298, c297, c43, c284, c22, c222, c192] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c889 := derived889 a h
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c890 := derived890 a h
  have h6 : Entails.eval a c891 := derived891 a h
  have h7 : Entails.eval a c298 := h 297 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c889, some c346, some c221, some c298, some c297, some c656, some c284, some c222, some c348, some c100, some c190, some c652, some c734, some c299, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c783, c878, c889, c346, c221, c298, c297, c656, c284, c222, c348, c100, c190, c652, c734, c299] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c889 := derived889 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c656 := derived656 a h
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c652 := derived652 a h
  have h14 : Entails.eval a c734 := derived734 a h
  have h15 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c97, some c123, some c893, some c131, some c892, some c307, some c346, some c559, some c180, some c314, some c142, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c783, c97, c123, c893, c131, c892, c307, c346, c559, c180, c314, c142] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c893 := derived893 a h
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c892 := derived892 a h
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c559 := derived559 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c314 := h 313 (by decide)
  have h11 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c97, some c123, some c221, some c892, some c307, some c893, some c131, some c894, some c99, some c117, some c241, some c116, some c600, some c182, some c261, some c142, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c878, c783, c97, c123, c221, c892, c307, c893, c131, c894, c99, c117, c241, c116, c600, c182, c261, c142] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c892 := derived892 a h
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c893 := derived893 a h
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c894 := derived894 a h
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c600 := derived600 a h
  have h15 : Entails.eval a c182 := h 181 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c180, some c182, some c117, some c116, some c241, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c878, c180, c182, c117, c116, c241] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c105, some c896, some c142, some c314, some c171, some c166, some c223, some c346, some c117, some c559, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c783, c878, c105, c896, c142, c314, c171, c166, c223, c346, c117, c559] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c896 := derived896 a h
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c559 := derived559 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c895, some c897, some c307, some c251, some c321, some c99, some c181, some c180, some c166, some c148, some c314, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c783, c895, c897, c307, c251, c321, c99, c181, c180, c166, c148, c314] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c897 := derived897 a h
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c251 := h 250 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c102, some c110, some c253, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c878, c102, c110, c253] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨22, by decide⟩, false), (⟨42, by decide⟩, true), (⟨13, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c243, some c248, some c114, some c198, some c213, some c328, some c340, some c208, some c215, some c250, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c199, c243, c248, c114, c198, c213, c328, c340, c208, c215, c250] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c103, some c254, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c111, c103, c254] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨42, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c895, some c899, some c901, some c248, some c900, some c198, some c148, some c147, some c330, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c878, c895, c899, c901, c248, c900, c198, c148, c147, c330] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c899 := derived899 a h
  have h3 : Entails.eval a c901 := derived901 a h
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c900 := derived900 a h
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c243, some c241, some c103, some c208, some c289, some c293, some c190, some c137, some c264, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c878, c243, c241, c103, c208, c289, c293, c190, c137, c264] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨31, by decide⟩, true), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c290, some c708, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c290, c708] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c290 := h 289 (by decide)
  have h1 : Entails.eval a c708 := derived708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c895, some c898, some c107, some c199, some c181, some c180, some c155, some c902, some c105, some c142, some c903, some c102, some c119, some c293, some c291, some c129, some c346, some c352, some c904, some c190, some c242, some c246, some c121, some c215, some c161, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c783, c878, c895, c898, c107, c199, c181, c180, c155, c902, c105, c142, c903, c102, c119, c293, c291, c129, c346, c352, c904, c190, c242, c246, c121, c215, c161] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c895 := derived895 a h
  have h3 : Entails.eval a c898 := derived898 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c902 := derived902 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c142 := h 141 (by decide)
  have h12 : Entails.eval a c903 := derived903 a h
  have h13 : Entails.eval a c102 := h 101 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c293 := h 292 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c346 := h 345 (by decide)
  have h19 : Entails.eval a c352 := h 351 (by decide)
  have h20 : Entails.eval a c904 := derived904 a h
  have h21 : Entails.eval a c190 := h 189 (by decide)
  have h22 : Entails.eval a c242 := h 241 (by decide)
  have h23 : Entails.eval a c246 := h 245 (by decide)
  have h24 : Entails.eval a c121 := h 120 (by decide)
  have h25 : Entails.eval a c215 := h 214 (by decide)
  have h26 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c129, some c103, some c232, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c783, c129, c103, c232] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c346, some c232, some c828, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c783, c346, c232, c828] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c828 := derived828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c905, some c895, some c181, some c180, some c906, some c293, some c102, some c907, some c559, some c231, some c120, some c114, some c243, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c878, c783, c905, c895, c181, c180, c906, c293, c102, c907, c559, c231, c120, c114, c243] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c895 := derived895 a h
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c906 := derived906 a h
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c907 := derived907 a h
  have h10 : Entails.eval a c559 := derived559 a h
  have h11 : Entails.eval a c231 := h 230 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c105, some c908, some c905, some c114, some c231, some c171, some c166, some c309, some c307, some c145, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c783, c878, c105, c908, c905, c114, c231, c171, c166, c309, c307, c145] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c905 := derived905 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c231 := h 230 (by decide)
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c166 := h 165 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨11, by decide⟩, true), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c289, some c293, some c135, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c878, c289, c293, c135] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c895, some c908, some c910, some c905, some c292, some c830, some c182, some c909, some c221, some c239, some c166, some c192, some c231, some c241, some c119, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c783, c878, c895, c908, c910, c905, c292, c830, c182, c909, c221, c239, c166, c192, c231, c241, c119] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c895 := derived895 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c910 := derived910 a h
  have h5 : Entails.eval a c905 := derived905 a h
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c830 := derived830 a h
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c909 := derived909 a h
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c166 := h 165 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c231 := h 230 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c895, some c905, some c908, some c910, some c911, some c650, some c656, some c352, some c232, some c654, some c196, some c249, some c240, some c194, some c909, some c294, some c296, some c543, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c783, c895, c905, c908, c910, c911, c650, c656, c352, c232, c654, c196, c249, c240, c194, c909, c294, c296, c543] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c910 := derived910 a h
  have h5 : Entails.eval a c911 := derived911 a h
  have h6 : Entails.eval a c650 := derived650 a h
  have h7 : Entails.eval a c656 := derived656 a h
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c654 := derived654 a h
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c909 := derived909 a h
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  have h18 : Entails.eval a c543 := derived543 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c912, some c443, some c895, some c910, some c656, some c830, some c290, some c837, some c135, some c848, some c834, some c165, some c105, some c307, some c253, some c145, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c783, c878, c912, c443, c895, c910, c656, c830, c290, c837, c135, c848, c834, c165, c105, c307, c253, c145] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c443 := derived443 a h
  have h4 : Entails.eval a c895 := derived895 a h
  have h5 : Entails.eval a c910 := derived910 a h
  have h6 : Entails.eval a c656 := derived656 a h
  have h7 : Entails.eval a c830 := derived830 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c837 := derived837 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c848 := derived848 a h
  have h12 : Entails.eval a c834 := derived834 a h
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c307 := h 306 (by decide)
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨31, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c895, some c912, some c443, some c656, some c292, some c105, some c113, some c899, some c245, some c247, some c192, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c783, c895, c912, c443, c656, c292, c105, c113, c899, c245, c247, c192] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c443 := derived443 a h
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c899 := derived899 a h
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨31, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c912, some c443, some c895, some c656, some c292, some c284, some c913, some c914, some c221, some c239, some c240, some c829, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c783, c912, c443, c895, c656, c292, c284, c913, c914, c221, c239, c240, c829] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c443 := derived443 a h
  have h3 : Entails.eval a c895 := derived895 a h
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c913 := derived913 a h
  have h8 : Entails.eval a c914 := derived914 a h
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c240 := h 239 (by decide)
  have h12 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨31, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c895, some c912, some c443, some c656, some c290, some c292, some c915, some c190, some c284, some c913, some c840, some c222, some c185, some c835, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c783, c895, c912, c443, c656, c290, c292, c915, c190, c284, c913, c840, c222, c185, c835] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c443 := derived443 a h
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c915 := derived915 a h
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c913 := derived913 a h
  have h11 : Entails.eval a c840 := derived840 a h
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c835 := derived835 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c912, some c443, some c895, some c656, some c292, some c290, some c915, some c190, some c916, some c105, some c113, some c899, some c247, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c783, c912, c443, c895, c656, c292, c290, c915, c190, c916, c105, c113, c899, c247] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c912 := derived912 a h
  have h2 : Entails.eval a c443 := derived443 a h
  have h3 : Entails.eval a c895 := derived895 a h
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c915 := derived915 a h
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c916 := derived916 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c899 := derived899 a h
  have h13 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c895, some c917, some c293, some c128, some c102, some c913, some c912, some c292, some c650, some c185, some c835, some c137, some c889, some c296, some c113, some c124, some c229, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c878, c895, c917, c293, c128, c102, c913, c912, c292, c650, c185, c835, c137, c889, c296, c113, c124, c229] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c917 := derived917 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c913 := derived913 a h
  have h7 : Entails.eval a c912 := derived912 a h
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c650 := derived650 a h
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c835 := derived835 a h
  have h12 : Entails.eval a c137 := h 136 (by decide)
  have h13 : Entails.eval a c889 := derived889 a h
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c124 := h 123 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c895, some c917, some c289, some c293, some c912, some c918, some c540, some c913, some c113, some c226, some c244, some c651, some c114, some c185, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c783, c895, c917, c289, c293, c912, c918, c540, c913, c113, c226, c244, c651, c114, c185] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c917 := derived917 a h
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c912 := derived912 a h
  have h6 : Entails.eval a c918 := derived918 a h
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c913 := derived913 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c651 := derived651 a h
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c895, some c912, some c917, some c289, some c293, some c102, some c918, some c540, some c919, some c834, some c241, some c100, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c878, c895, c912, c917, c289, c293, c102, c918, c540, c919, c834, c241, c100] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c895 := derived895 a h
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c917 := derived917 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c918 := derived918 a h
  have h8 : Entails.eval a c540 := derived540 a h
  have h9 : Entails.eval a c919 := derived919 a h
  have h10 : Entails.eval a c834 := derived834 a h
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c176, some c178, some c832, some c830, some c196, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c920, c176, c178, c832, c830, c196] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c832 := derived832 a h
  have h4 : Entails.eval a c830 := derived830 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c920, some c878, some c240, some c239, some c221, some c226, some c244, some c124, some c651, some c178, some c176, some c921, some c37, some c720, some c784, some c194, some c295, some c298, some c135, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c783, c920, c878, c240, c239, c221, c226, c244, c124, c651, c178, c176, c921, c37, c720, c784, c194, c295, c298, c135] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c244 := h 243 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c651 := derived651 a h
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c921 := derived921 a h
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c720 := derived720 a h
  have h15 : Entails.eval a c784 := derived784 a h
  have h16 : Entails.eval a c194 := h 193 (by decide)
  have h17 : Entails.eval a c295 := h 294 (by decide)
  have h18 : Entails.eval a c298 := h 297 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c878, some c240, some c239, some c221, some c922, some c115, some c98, some c178, some c176, some c921, some c37, some c720, some c784, some c280, some c231, some c194, some c295, some c298, some c135, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c920, c783, c878, c240, c239, c221, c922, c115, c98, c178, c176, c921, c37, c720, c784, c280, c231, c194, c295, c298, c135] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c922 := derived922 a h
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c921 := derived921 a h
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c720 := derived720 a h
  have h14 : Entails.eval a c784 := derived784 a h
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c231 := h 230 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c878, some c240, some c239, some c221, some c178, some c921, some c37, some c720, some c784, some c280, some c351, some c231, some c279, some c194, some c295, some c298, some c135, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c920, c783, c878, c240, c239, c221, c178, c921, c37, c720, c784, c280, c351, c231, c279, c194, c295, c298, c135] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c239 := h 238 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c720 := derived720 a h
  have h10 : Entails.eval a c784 := derived784 a h
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c351 := h 350 (by decide)
  have h13 : Entails.eval a c231 := h 230 (by decide)
  have h14 : Entails.eval a c279 := h 278 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c298 := h 297 (by decide)
  have h18 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨40, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c100, some c265, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c108, c100, c265] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c280, some c101, some c231, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c783, c280, c101, c231] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c920, some c923, some c650, some c240, some c112, some c121, some c241, some c925, some c182, some c221, some c37, some c19, some c2, some c926, some c300, some c299, some c48, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c783, c878, c920, c923, c650, c240, c112, c121, c241, c925, c182, c221, c37, c19, c2, c926, c300, c299, c48] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c923 := derived923 a h
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c240 := h 239 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c925 := derived925 a h
  have h10 : Entails.eval a c182 := h 181 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c926 := derived926 a h
  have h16 : Entails.eval a c300 := h 299 (by decide)
  have h17 : Entails.eval a c299 := h 298 (by decide)
  have h18 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c920, some c240, some c239, some c924, some c650, some c121, some c241, some c927, some c832, some c292, some c192, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c878, c920, c240, c239, c924, c650, c121, c241, c927, c832, c292, c192] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c924 := derived924 a h
  have h5 : Entails.eval a c650 := derived650 a h
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c927 := derived927 a h
  have h9 : Entails.eval a c832 := derived832 a h
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c239, some c240, some c928, some c176, some c175, some c122, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c920, c239, c240, c928, c176, c175, c122] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c928 := derived928 a h
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c175, some c653, some c352, some c232, some c651, some c122, some c180, some c249, some c120, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c920, c783, c175, c653, c352, c232, c651, c122, c180, c249, c120] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c651 := derived651 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c652, some c653, some c111, some c315, some c320, some c145, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c783, c878, c652, c653, c111, c315, c320, c145] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c920, some c352, some c651, some c930, some c931, some c652, some c929, some c145, some c320, some c203, some c336, some c153, some c158, some c57, some c213, some c31, some c24, some c647, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c878, c783, c920, c352, c651, c930, c931, c652, c929, c145, c320, c203, c336, c153, c158, c57, c213, c31, c24, c647] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c651 := derived651 a h
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c931 := derived931 a h
  have h7 : Entails.eval a c652 := derived652 a h
  have h8 : Entails.eval a c929 := derived929 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c647 := derived647 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c930, some c931, some c249, some c650, some c929, some c352, some c651, some c932, some c315, some c203, some c211, some c153, some c158, some c326, some c331, some c314, some c214, some c56, some c302, some c412, some c278, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c920, c783, c930, c931, c249, c650, c929, c352, c651, c932, c315, c203, c211, c153, c158, c326, c331, c314, c214, c56, c302, c412, c278] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c930 := derived930 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c650 := derived650 a h
  have h6 : Entails.eval a c929 := derived929 a h
  have h7 : Entails.eval a c352 := h 351 (by decide)
  have h8 : Entails.eval a c651 := derived651 a h
  have h9 : Entails.eval a c932 := derived932 a h
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c211 := h 210 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c331 := h 330 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c214 := h 213 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c302 := h 301 (by decide)
  have h21 : Entails.eval a c412 := derived412 a h
  have h22 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c650, some c203, some c211, some c153, some c326, some c331, some c314, some c214, some c143, some c158, some c56, some c302, some c412, some c278, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c920, c783, c650, c203, c211, c153, c326, c331, c314, c214, c143, c158, c56, c302, c412, c278] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c650 := derived650 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c153 := h 152 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c302 := h 301 (by decide)
  have h14 : Entails.eval a c412 := derived412 a h
  have h15 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨45, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c302, some c412, some c278, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c56, c302, c412, c278] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c920, some c878, some c650, some c934, some c321, some c327, some c206, some c197, some c205, some c331, some c314, some c153, some c143, some c219, some c935, some c344, some c157, some c217, some c119, some c247, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c783, c920, c878, c650, c934, c321, c327, c206, c197, c205, c331, c314, c153, c143, c219, c935, c344, c157, c217, c119, c247] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c650 := derived650 a h
  have h4 : Entails.eval a c934 := derived934 a h
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c219 := h 218 (by decide)
  have h15 : Entails.eval a c935 := derived935 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c217 := h 216 (by decide)
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨10, by decide⟩, false), (⟨47, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c219, some c344, some c157, some c217, some c119, some c247, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c878, c219, c344, c157, c217, c119, c247] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨55, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c920, some c783, some c930, some c929, some c931, some c936, some c145, some c650, some c330, some c325, some c205, some c206, some c197, some c226, some c153, some c651, some c219, some c937, some c56, some c24, some c522, some c57, some c188, some c335, some c266, some c935, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c878, c920, c783, c930, c929, c931, c936, c145, c650, c330, c325, c205, c206, c197, c226, c153, c651, c219, c937, c56, c24, c522, c57, c188, c335, c266, c935] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c783 := derived783 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c929 := derived929 a h
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c936 := derived936 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c650 := derived650 a h
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c325 := h 324 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c226 := h 225 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c651 := derived651 a h
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c937 := derived937 a h
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  have h21 : Entails.eval a c522 := derived522 a h
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c188 := h 187 (by decide)
  have h24 : Entails.eval a c335 := h 334 (by decide)
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c935 := derived935 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, false), (⟨47, by decide⟩, false), (⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c878, some c153, some c158, some c182, some c213, some c119, some c247, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c920, c878, c153, c158, c182, c213, c119, c247] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c920, some c783, some c249, some c930, some c652, some c929, some c931, some c933, some c936, some c145, some c938, some c203, some c153, some c197, some c323, some c144, some c210, some c939, some c651, some c226, some c313, some c106, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c878, c920, c783, c249, c930, c652, c929, c931, c933, c936, c145, c938, c203, c153, c197, c323, c144, c210, c939, c651, c226, c313, c106] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c920 := derived920 a h
  have h2 : Entails.eval a c783 := derived783 a h
  have h3 : Entails.eval a c249 := h 248 (by decide)
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c652 := derived652 a h
  have h6 : Entails.eval a c929 := derived929 a h
  have h7 : Entails.eval a c931 := derived931 a h
  have h8 : Entails.eval a c933 := derived933 a h
  have h9 : Entails.eval a c936 := derived936 a h
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c938 := derived938 a h
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c939 := derived939 a h
  have h19 : Entails.eval a c651 := derived651 a h
  have h20 : Entails.eval a c226 := h 225 (by decide)
  have h21 : Entails.eval a c313 := h 312 (by decide)
  have h22 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c652, some c651, some c106, some c313, some c311, some c145, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c783, c878, c652, c651, c106, c313, c311, c145] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c651 := derived651 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, true), (⟨21, by decide⟩, true), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c145, some c313, some c329, some c144, some c182, some c101, some c109, some c258, some c187, some c571, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c878, c145, c313, c329, c144, c182, c101, c109, c258, c187, c571] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c571 := derived571 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, true), (⟨21, by decide⟩, true), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c145, some c942, some c205, some c198, some c325, some c323, some c158, some c144, some c304, some c156, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c878, c145, c942, c205, c198, c325, c323, c158, c144, c304, c156] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c942 := derived942 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c920, some c941, some c650, some c205, some c198, some c322, some c321, some c307, some c158, some c149, some c61, some c323, some c4, some c304, some c37, some c156, some c830, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c783, c878, c920, c941, c650, c205, c198, c322, c321, c307, c158, c149, c61, c323, c4, c304, c37, c156, c830] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c941 := derived941 a h
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c322 := h 321 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c149 := h 148 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c304 := h 303 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c920, some c930, some c652, some c650, some c929, some c249, some c940, some c232, some c245, some c653, some c941, some c943, some c944, some c326, some c109, some c206, some c182, some c307, some c808, some c830, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c878, c783, c920, c930, c652, c650, c929, c249, c940, c232, c245, c653, c941, c943, c944, c326, c109, c206, c182, c307, c808, c830] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c930 := derived930 a h
  have h4 : Entails.eval a c652 := derived652 a h
  have h5 : Entails.eval a c650 := derived650 a h
  have h6 : Entails.eval a c929 := derived929 a h
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c940 := derived940 a h
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c653 := derived653 a h
  have h12 : Entails.eval a c941 := derived941 a h
  have h13 : Entails.eval a c943 := derived943 a h
  have h14 : Entails.eval a c944 := derived944 a h
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c206 := h 205 (by decide)
  have h18 : Entails.eval a c182 := h 181 (by decide)
  have h19 : Entails.eval a c307 := h 306 (by decide)
  have h20 : Entails.eval a c808 := derived808 a h
  have h21 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨40, by decide⟩, false), (⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c878, some c920, some c652, some c650, some c944, some c322, some c263, some c331, some c311, some c327, some c197, some c135, some c153, some c61, some c4, some c10, some c64, some c75, some c647, some c38, some c96, some c348, some c297, some c40, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c783, c878, c920, c652, c650, c944, c322, c263, c331, c311, c327, c197, c135, c153, c61, c4, c10, c64, c75, c647, c38, c96, c348, c297, c40] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c878 := derived878 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c652 := derived652 a h
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c944 := derived944 a h
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c135 := h 134 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c647 := derived647 a h
  have h20 : Entails.eval a c38 := h 37 (by decide)
  have h21 : Entails.eval a c96 := h 95 (by decide)
  have h22 : Entails.eval a c348 := h 347 (by decide)
  have h23 : Entails.eval a c297 := h 296 (by decide)
  have h24 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨53, by decide⟩, true), (⟨35, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c145, some c313, some c329, some c144, some c182, some c127, some c299, some c135, some c259, some c187, some c571, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c878, c145, c313, c329, c144, c182, c127, c299, c135, c259, c187, c571] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c571 := derived571 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c783, some c920, some c945, some c112, some c930, some c652, some c650, some c929, some c232, some c245, some c653, some c115, some c946, some c145, some c943, some c231, some c947, some c205, some c198, some c309, some c255, some c325, some c158, some c37, some c61, some c4, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c878, c783, c920, c945, c112, c930, c652, c650, c929, c232, c245, c653, c115, c946, c145, c943, c231, c947, c205, c198, c309, c255, c325, c158, c37, c61, c4] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c920 := derived920 a h
  have h3 : Entails.eval a c945 := derived945 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c652 := derived652 a h
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c929 := derived929 a h
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c653 := derived653 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c946 := derived946 a h
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c943 := derived943 a h
  have h16 : Entails.eval a c231 := h 230 (by decide)
  have h17 : Entails.eval a c947 := derived947 a h
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c198 := h 197 (by decide)
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c255 := h 254 (by decide)
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c158 := h 157 (by decide)
  have h24 : Entails.eval a c37 := h 36 (by decide)
  have h25 : Entails.eval a c61 := h 60 (by decide)
  have h26 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨38, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c198, some c325, some c158, some c203, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c205, c198, c325, c158, c203] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c949, some c330, some c203, some c153, some c158, some c213, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c920, c949, c330, c203, c153, c158, c213] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨40, by decide⟩, false), (⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c946, some c145, some c950, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c878, c946, c145, c950] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c950 := derived950 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c945, some c948, some c122, some c112, some c121, some c930, some c650, some c929, some c951, some c244, some c247, some c925, some c182, some c101, some c109, some c266, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c878, c945, c948, c122, c112, c121, c930, c650, c929, c951, c244, c247, c925, c182, c101, c109, c266] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c948 := derived948 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c929 := derived929 a h
  have h9 : Entails.eval a c951 := derived951 a h
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c925 := derived925 a h
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c783, some c945, some c952, some c651, some c115, some c226, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c783, c945, c952, c651, c115, c226] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c783 := derived783 a h
  have h1 : Entails.eval a c945 := derived945 a h
  have h2 : Entails.eval a c952 := derived952 a h
  have h3 : Entails.eval a c651 := derived651 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨26, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c176, some c178, some c294, some c296, some c134, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c920, c176, c178, c294, c296, c134] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c953, some c176, some c178, some c929, some c188, some c830, some c910, some c194, some c656, some c232, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c920, c783, c953, c176, c178, c929, c188, c830, c910, c194, c656, c232] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c953 := derived953 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c178 := h 177 (by decide)
  have h5 : Entails.eval a c929 := derived929 a h
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c830 := derived830 a h
  have h8 : Entails.eval a c910 := derived910 a h
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c656 := derived656 a h
  have h11 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c783, some c878, some c953, some c176, some c178, some c954, some c955, some c231, some c716, some c646, some c830, some c280, some c346, some c286, some c295, some c298, some c135, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c920, c783, c878, c953, c176, c178, c954, c955, c231, c716, c646, c830, c280, c346, c286, c295, c298, c135] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c783 := derived783 a h
  have h2 : Entails.eval a c878 := derived878 a h
  have h3 : Entails.eval a c953 := derived953 a h
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  have h6 : Entails.eval a c954 := derived954 a h
  have h7 : Entails.eval a c955 := derived955 a h
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c716 := derived716 a h
  have h10 : Entails.eval a c646 := derived646 a h
  have h11 : Entails.eval a c830 := derived830 a h
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c920, some c956, some c953, some c176, some c178, some c929, some c786, some c249, some c187, some c189, some c830, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c920, c956, c953, c176, c178, c929, c786, c249, c187, c189, c830] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c920 := derived920 a h
  have h1 : Entails.eval a c956 := derived956 a h
  have h2 : Entails.eval a c953 := derived953 a h
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c178 := h 177 (by decide)
  have h5 : Entails.eval a c929 := derived929 a h
  have h6 : Entails.eval a c786 := derived786 a h
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived957

end CochromaticTwenty.Certificates.B16_7_1
