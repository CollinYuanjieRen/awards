import MerLeanExperiment.Certificates.B16_6_1.Inputs

/-! Generated from the actual pinned b16_6_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c374 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c359, some c340, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked374 : lratChecker f374 p374 = .success := by decide +kernel
theorem unsat374 : Unsatisfiable (PosFin 57) f374 := by
  apply lratCheckerSound f374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p374
  · intro a ha; simp [p374] at ha; subst a; trivial
  · exact checked374
theorem derived374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c374 := by
  apply localUnsat_implies_entails f374 [c354, c359, c340] c374 unsat374 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c375 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c353, some c343, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked375 : lratChecker f375 p375 = .success := by decide +kernel
theorem unsat375 : Unsatisfiable (PosFin 57) f375 := by
  apply lratCheckerSound f375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p375
  · intro a ha; simp [p375] at ha; subst a; trivial
  · exact checked375
theorem derived375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c375 := by
  apply localUnsat_implies_entails f375 [c350, c353, c343] c375 unsat375 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c376 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c73, some c328, some c57, some c205, some c303, some c28, some c331, some c203, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked376 : lratChecker f376 p376 = .success := by decide +kernel
theorem unsat376 : Unsatisfiable (PosFin 57) f376 := by
  apply lratCheckerSound f376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p376
  · intro a ha; simp [p376] at ha; subst a; trivial
  · exact checked376
theorem derived376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c376 := by
  apply localUnsat_implies_entails f376 [c372, c73, c328, c57, c205, c303, c28, c331, c203] c376 unsat376 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c377 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c372, some c371, some c366, some c374, some c375, some c71, some c340, some c356, some c73, some c343, some c99, some c100, some c357, some c376, some c70, some c329, some c58, some c206, some c306, some c21, some c330, some c201, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked377 : lratChecker f377 p377 = .success := by decide +kernel
theorem unsat377 : Unsatisfiable (PosFin 57) f377 := by
  apply lratCheckerSound f377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p377
  · intro a ha; simp [p377] at ha; subst a; trivial
  · exact checked377
theorem derived377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c377 := by
  apply localUnsat_implies_entails f377 [c373, c372, c371, c366, c374, c375, c71, c340, c356, c73, c343, c99, c100, c357, c376, c70, c329, c58, c206, c306, c21, c330, c201] c377 unsat377 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c374 := derived374 a h
  have h5 : Entails.eval a c375 := derived375 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c376 := derived376 a h
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c306 := h 305 (by decide)
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c330 := h 329 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c378 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c71, some c372, some c73, some c376, some c99, some c100, some c70, some c86, some c329, some c104, some c306, some c308, some c63, some c334, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked378 : lratChecker f378 p378 = .success := by decide +kernel
theorem unsat378 : Unsatisfiable (PosFin 57) f378 := by
  apply lratCheckerSound f378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p378
  · intro a ha; simp [p378] at ha; subst a; trivial
  · exact checked378
theorem derived378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c378 := by
  apply localUnsat_implies_entails f378 [c366, c71, c372, c73, c376, c99, c100, c70, c86, c329, c104, c306, c308, c63, c334] c378 unsat378 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c376 := derived376 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c308 := h 307 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c379 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c92, some c267, some c101, some c36, some c85, some c106, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked379 : lratChecker f379 p379 = .success := by decide +kernel
theorem unsat379 : Unsatisfiable (PosFin 57) f379 := by
  apply lratCheckerSound f379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p379
  · intro a ha; simp [p379] at ha; subst a; trivial
  · exact checked379
theorem derived379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c379 := by
  apply localUnsat_implies_entails f379 [c37, c92, c267, c101, c36, c85, c106] c379 unsat379 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c380 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c71, some c373, some c372, some c371, some c357, some c358, some c378, some c379, some c99, some c59, some c86, some c329, some c104, some c58, some c36, some c101, some c268, some c38, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked380 : lratChecker f380 p380 = .success := by decide +kernel
theorem unsat380 : Unsatisfiable (PosFin 57) f380 := by
  apply lratCheckerSound f380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p380
  · intro a ha; simp [p380] at ha; subst a; trivial
  · exact checked380
theorem derived380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c380 := by
  apply localUnsat_implies_entails f380 [c366, c71, c373, c372, c371, c357, c358, c378, c379, c99, c59, c86, c329, c104, c58, c36, c101, c268, c38] c380 unsat380 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c378 := derived378 a h
  have h8 : Entails.eval a c379 := derived379 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c329 := h 328 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c381 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨45, by decide⟩, true), (⟨4, by decide⟩, false), (⟨41, by decide⟩, true), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c71, some c102, some c101, some c99, some c59, some c86, some c329, some c69, some c328, some c205, some c303, some c28, some c30, some c331, some c333, some c210, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked381 : lratChecker f381 p381 = .success := by decide +kernel
theorem unsat381 : Unsatisfiable (PosFin 57) f381 := by
  apply lratCheckerSound f381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p381
  · intro a ha; simp [p381] at ha; subst a; trivial
  · exact checked381
theorem derived381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c381 := by
  apply localUnsat_implies_entails f381 [c366, c71, c102, c101, c99, c59, c86, c329, c69, c328, c205, c303, c28, c30, c331, c333, c210] c381 unsat381 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c382 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c372, some c371, some c380, some c74, some c343, some c355, some c381, some c37, some c267, some c36, some c132, some c158, some c7, some c173, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked382 : lratChecker f382 p382 = .success := by decide +kernel
theorem unsat382 : Unsatisfiable (PosFin 57) f382 := by
  apply lratCheckerSound f382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p382
  · intro a ha; simp [p382] at ha; subst a; trivial
  · exact checked382
theorem derived382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c382 := by
  apply localUnsat_implies_entails f382 [c373, c372, c371, c380, c74, c343, c355, c381, c37, c267, c36, c132, c158, c7, c173] c382 unsat382 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c380 := derived380 a h
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c381 := derived381 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c383 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c353, some c343, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked383 : lratChecker f383 p383 = .success := by decide +kernel
theorem unsat383 : Unsatisfiable (PosFin 57) f383 := by
  apply lratCheckerSound f383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p383
  · intro a ha; simp [p383] at ha; subst a; trivial
  · exact checked383
theorem derived383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c383 := by
  apply localUnsat_implies_entails f383 [c351, c353, c343] c383 unsat383 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c384 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c372, some c371, some c366, some c377, some c383, some c340, some c382, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked384 : lratChecker f384 p384 = .success := by decide +kernel
theorem unsat384 : Unsatisfiable (PosFin 57) f384 := by
  apply lratCheckerSound f384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p384
  · intro a ha; simp [p384] at ha; subst a; trivial
  · exact checked384
theorem derived384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c384 := by
  apply localUnsat_implies_entails f384 [c373, c372, c371, c366, c377, c383, c340, c382] c384 unsat384 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c377 := derived377 a h
  have h5 : Entails.eval a c383 := derived383 a h
  have h6 : Entails.eval a c340 := h 339 (by decide)
  have h7 : Entails.eval a c382 := derived382 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c385 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c105, some c86, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked385 : lratChecker f385 p385 = .success := by decide +kernel
theorem unsat385 : Unsatisfiable (PosFin 57) f385 := by
  apply lratCheckerSound f385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p385
  · intro a ha; simp [p385] at ha; subst a; trivial
  · exact checked385
theorem derived385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c385 := by
  apply localUnsat_implies_entails f385 [c104, c105, c86] c385 unsat385 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c386 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨45, by decide⟩, true), (⟨4, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c89, some c102, some c99, some c88, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked386 : lratChecker f386 p386 = .success := by decide +kernel
theorem unsat386 : Unsatisfiable (PosFin 57) f386 := by
  apply lratCheckerSound f386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p386
  · intro a ha; simp [p386] at ha; subst a; trivial
  · exact checked386
theorem derived386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c386 := by
  apply localUnsat_implies_entails f386 [c385, c89, c102, c99, c88] c386 unsat386 (by rfl) a
  have h0 : Entails.eval a c385 := derived385 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c387 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c343, some c355, some c386, some c37, some c262, some c267, some c280, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked387 : lratChecker f387 p387 = .success := by decide +kernel
theorem unsat387 : Unsatisfiable (PosFin 57) f387 := by
  apply lratCheckerSound f387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p387
  · intro a ha; simp [p387] at ha; subst a; trivial
  · exact checked387
theorem derived387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c387 := by
  apply localUnsat_implies_entails f387 [c74, c343, c355, c386, c37, c262, c267, c280] c387 unsat387 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c386 := derived386 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c388 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c379, some c262, some c35, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked388 : lratChecker f388 p388 = .success := by decide +kernel
theorem unsat388 : Unsatisfiable (PosFin 57) f388 := by
  apply lratCheckerSound f388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p388
  · intro a ha; simp [p388] at ha; subst a; trivial
  · exact checked388
theorem derived388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c388 := by
  apply localUnsat_implies_entails f388 [c37, c379, c262, c35] c388 unsat388 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c379 := derived379 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c389 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c385, some c386, some c36, some c38, some c268, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 57) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c357, c385, c386, c36, c38, c268] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c385 := derived385 a h
  have h2 : Entails.eval a c386 := derived386 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c390 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c352, some c357, some c389, some c73, some c388, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 57) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c387, c352, c357, c389, c73, c388] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c387 := derived387 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c389 := derived389 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c388 := derived388 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c391 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c373, some c372, some c371, some c366, some c382, some c390, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 57) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c384, c373, c372, c371, c366, c382, c390] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c384 := derived384 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c390 := derived390 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c372, some c385, some c37, some c92, some c262, some c106, some c35, some c57, some c102, some c328, some c60, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 57) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c373, c372, c385, c37, c92, c262, c106, c35, c57, c102, c328, c60] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c385 := derived385 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨45, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c72, some c37, some c92, some c262, some c272, some c106, some c107, some c35, some c131, some c280, some c49, some c2, some c298, some c134, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 57) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c340, c72, c37, c92, c262, c272, c106, c107, c35, c131, c280, c49, c2, c298, c134] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c72, some c373, some c372, some c392, some c393, some c105, some c88, some c100, some c35, some c262, some c133, some c153, some c6, some c170, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 57) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c340, c72, c373, c372, c392, c393, c105, c88, c100, c35, c262, c133, c153, c6, c170] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c392 := derived392 a h
  have h5 : Entails.eval a c393 := derived393 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c373, some c372, some c371, some c366, some c391, some c72, some c340, some c394, some c73, some c343, some c104, some c105, some c352, some c59, some c88, some c329, some c100, some c306, some c310, some c331, some c338, some c62, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 57) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c384, c373, c372, c371, c366, c391, c72, c340, c394, c73, c343, c104, c105, c352, c59, c88, c329, c100, c306, c310, c331, c338, c62] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c384 := derived384 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c391 := derived391 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  have h8 : Entails.eval a c394 := derived394 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c100 := h 99 (by decide)
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c310 := h 309 (by decide)
  have h20 : Entails.eval a c331 := h 330 (by decide)
  have h21 : Entails.eval a c338 := h 337 (by decide)
  have h22 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c73, some c105, some c104, some c343, some c265, some c263, some c50, some c38, some c134, some c283, some c295, some c7, some c132, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 57) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c350, c73, c105, c104, c343, c265, c263, c50, c38, c134, c283, c295, c7, c132] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c340, some c350, some c73, some c343, some c396, some c35, some c131, some c1, some c154, some c173, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 57) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c72, c340, c350, c73, c343, c396, c35, c131, c1, c154, c173] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c350 := h 349 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c396 := derived396 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c397, some c356, some c343, some c357, some c73, some c374, some c104, some c396, some c85, some c35, some c280, some c101, some c268, some c38, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 57) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c397, c356, c343, c357, c73, c374, c104, c396, c85, c35, c280, c101, c268, c38] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c397 := derived397 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c374 := derived374 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c396 := derived396 a h
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨3, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c89, some c268, some c100, some c38, some c87, some c101, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 57) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c36, c89, c268, c100, c38, c87, c101] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c366, some c372, some c373, some c384, some c395, some c374, some c397, some c356, some c73, some c343, some c357, some c399, some c398, some c71, some c376, some c100, some c60, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 57) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c371, c366, c372, c373, c384, c395, c374, c397, c356, c73, c343, c357, c399, c398, c71, c376, c100, c60] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c384 := derived384 a h
  have h5 : Entails.eval a c395 := derived395 a h
  have h6 : Entails.eval a c374 := derived374 a h
  have h7 : Entails.eval a c397 := derived397 a h
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c399 := derived399 a h
  have h13 : Entails.eval a c398 := derived398 a h
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c376 := derived376 a h
  have h16 : Entails.eval a c100 := h 99 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c366, some c71, some c341, some c357, some c74, some c343, some c101, some c102, some c83, some c58, some c99, some c329, some c70, some c324, some c203, some c305, some c19, some c332, some c201, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 57) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c400, c366, c71, c341, c357, c74, c343, c101, c102, c83, c58, c99, c329, c70, c324, c203, c305, c19, c332, c201] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c329 := h 328 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c305 := h 304 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c332 := h 331 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨1, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c374, some c74, some c101, some c102, some c83, some c58, some c99, some c329, some c70, some c324, some c203, some c305, some c230, some c19, some c332, some c123, some c119, some c156, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 57) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c366, c371, c374, c74, c101, c102, c83, c58, c99, c329, c70, c324, c203, c305, c230, c19, c332, c123, c119, c156] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c230 := h 229 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c332 := h 331 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨48, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c399, some c104, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 57) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c399, c104] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c399 := derived399 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c404 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c374, some c356, some c401, some c400, some c402, some c353, some c357, some c75, some c403, some c83, some c101, some c38, some c263, some c268, some c280, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 57) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c366, c371, c374, c356, c401, c400, c402, c353, c357, c75, c403, c83, c101, c38, c263, c268, c280] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c401 := derived401 a h
  have h5 : Entails.eval a c400 := derived400 a h
  have h6 : Entails.eval a c402 := derived402 a h
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c403 := derived403 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c89, some c90, some c106, some c38, some c74, some c263, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 57) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c35, c89, c90, c106, c38, c74, c263] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c366, some c371, some c374, some c400, some c401, some c405, some c404, some c73, some c343, some c383, some c398, some c399, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 57) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c356, c366, c371, c374, c400, c401, c405, c404, c73, c343, c383, c398, c399] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c374 := derived374 a h
  have h4 : Entails.eval a c400 := derived400 a h
  have h5 : Entails.eval a c401 := derived401 a h
  have h6 : Entails.eval a c405 := derived405 a h
  have h7 : Entails.eval a c404 := derived404 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c383 := derived383 a h
  have h11 : Entails.eval a c398 := derived398 a h
  have h12 : Entails.eval a c399 := derived399 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c99, some c353, some c357, some c87, some c75, some c101, some c104, some c36, some c271, some c268, some c48, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 57) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c100, c99, c353, c357, c87, c75, c101, c104, c36, c271, c268, c48] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨44, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, false), (⟨46, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c60, some c101, some c327, some c56, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 57) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c87, c60, c101, c327, c56] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c131, some c281, some c1, some c300, some c133, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 57) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c266, c131, c281, c1, c300, c133] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c271, some c280, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 57) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c265, c271, c280] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c73, some c374, some c407, some c409, some c408, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 57) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c356, c73, c374, c407, c409, c408] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c407 := derived407 a h
  have h4 : Entails.eval a c409 := derived409 a h
  have h5 : Entails.eval a c408 := derived408 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c90, some c104, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 57) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c89, c90, c104] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c73, some c412, some c99, some c410, some c411, some c52, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 57) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c356, c73, c412, c99, c410, c411, c52] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c410 := derived410 a h
  have h5 : Entails.eval a c411 := derived411 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c73, some c412, some c413, some c100, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 57) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c356, c73, c412, c413, c100] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c413 := derived413 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c102, some c55, some c83, some c82, some c323, some c324, some c103, some c353, some c66, some c310, some c326, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 57) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c100, c102, c55, c83, c82, c323, c324, c103, c353, c66, c310, c326] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c323 := h 322 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨31, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c89, some c90, some c412, some c106, some c83, some c82, some c108, some c263, some c48, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 57) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c35, c89, c90, c412, c106, c83, c82, c108, c263, c48] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c412 := derived412 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c83, some c323, some c324, some c103, some c70, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 57) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c55, c83, c323, c324, c103, c70] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c406, some c356, some c366, some c371, some c374, some c400, some c410, some c414, some c416, some c415, some c417, some c99, some c407, some c52, some c408, some c266, some c131, some c281, some c1, some c156, some c300, some c117, some c113, some c230, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 57) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c406, c356, c366, c371, c374, c400, c410, c414, c416, c415, c417, c99, c407, c52, c408, c266, c131, c281, c1, c156, c300, c117, c113, c230] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c406 := derived406 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c374 := derived374 a h
  have h5 : Entails.eval a c400 := derived400 a h
  have h6 : Entails.eval a c410 := derived410 a h
  have h7 : Entails.eval a c414 := derived414 a h
  have h8 : Entails.eval a c416 := derived416 a h
  have h9 : Entails.eval a c415 := derived415 a h
  have h10 : Entails.eval a c417 := derived417 a h
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c407 := derived407 a h
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c408 := derived408 a h
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c281 := h 280 (by decide)
  have h18 : Entails.eval a c1 := h 0 (by decide)
  have h19 : Entails.eval a c156 := h 155 (by decide)
  have h20 : Entails.eval a c300 := h 299 (by decide)
  have h21 : Entails.eval a c117 := h 116 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c52, some c278, some c39, some c135, some c281, some c160, some c11, some c293, some c291, some c170, some c48, some c142, some c2, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 57) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c99, c52, c278, c39, c135, c281, c160, c11, c293, c291, c170, c48, c142, c2] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c281 := h 280 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c142 := h 141 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c419, some c271, some c36, some c132, some c280, some c104, some c6, some c160, some c290, some c294, some c39, some c171, some c143, some c278, some c3, some c51, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 57) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c419, c271, c36, c132, c280, c104, c6, c160, c290, c294, c39, c171, c143, c278, c3, c51] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c419 := derived419 a h
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c278 := h 277 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c366, some c418, some c341, some c357, some c71, some c406, some c356, some c371, some c374, some c408, some c420, some c73, some c417, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 57) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c400, c366, c418, c341, c357, c71, c406, c356, c371, c374, c408, c420, c73, c417] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c406 := derived406 a h
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c374 := derived374 a h
  have h10 : Entails.eval a c408 := derived408 a h
  have h11 : Entails.eval a c420 := derived420 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c417 := derived417 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c366, some c356, some c418, some c71, some c341, some c357, some c421, some c100, some c102, some c82, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 57) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c400, c366, c356, c418, c71, c341, c357, c421, c100, c102, c82] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c418 := derived418 a h
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c421 := derived421 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c102, some c73, some c55, some c83, some c82, some c323, some c324, some c103, some c353, some c66, some c304, some c310, some c337, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 57) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c100, c102, c73, c55, c83, c82, c323, c324, c103, c353, c66, c304, c310, c337] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c310 := h 309 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c374, some c35, some c416, some c265, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 57) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c350, c374, c35, c416, c265] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c416 := derived416 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c417, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 57) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c73, c417] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c417 := derived417 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c426 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨3, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c424, some c265, some c131, some c280, some c281, some c299, some c296, some c297, some c1, some c143, some c142, some c182, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 57) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c424, c265, c131, c280, c281, c299, c296, c297, c1, c143, c142, c182] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c371, some c366, some c374, some c422, some c72, some c340, some c350, some c424, some c423, some c425, some c99, some c104, some c75, some c426, some c39, some c52, some c278, some c301, some c87, some c48, some c101, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 57) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c400, c371, c366, c374, c422, c72, c340, c350, c424, c423, c425, c99, c104, c75, c426, c39, c52, c278, c301, c87, c48, c101] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c374 := derived374 a h
  have h4 : Entails.eval a c422 := derived422 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c340 := h 339 (by decide)
  have h7 : Entails.eval a c350 := h 349 (by decide)
  have h8 : Entails.eval a c424 := derived424 a h
  have h9 : Entails.eval a c423 := derived423 a h
  have h10 : Entails.eval a c425 := derived425 a h
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c426 := derived426 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c278 := h 277 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c48 := h 47 (by decide)
  have h21 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c427, some c425, some c385, some c99, some c59, some c88, some c329, some c361, some c58, some c84, some c101, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 57) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c427, c425, c385, c99, c59, c88, c329, c361, c58, c84, c101] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c427 := derived427 a h
  have h1 : Entails.eval a c425 := derived425 a h
  have h2 : Entails.eval a c385 := derived385 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c329 := h 328 (by decide)
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c104, some c59, some c84, some c329, some c101, some c69, some c67, some c338, some c339, some c305, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 57) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c99, c104, c59, c84, c329, c101, c69, c67, c338, c339, c305] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c338 := h 337 (by decide)
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c366, some c340, some c72, some c427, some c428, some c352, some c429, some c73, some c55, some c82, some c323, some c324, some c101, some c59, some c207, some c307, some c69, some c22, some c27, some c332, some c337, some c208, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 57) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c371, c366, c340, c72, c427, c428, c352, c429, c73, c55, c82, c323, c324, c101, c59, c207, c307, c69, c22, c27, c332, c337, c208] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c427 := derived427 a h
  have h5 : Entails.eval a c428 := derived428 a h
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c429 := derived429 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c22 := h 21 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  have h20 : Entails.eval a c332 := h 331 (by decide)
  have h21 : Entails.eval a c337 := h 336 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, false), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c72, some c106, some c39, some c75, some c272, some c47, some c264, some c131, some c280, some c153, some c2, some c297, some c142, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 57) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c340, c72, c106, c39, c75, c272, c47, c264, c131, c280, c153, c2, c297, c142] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c280 := h 279 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c366, some c340, some c427, some c400, some c430, some c351, some c60, some c88, some c99, some c103, some c87, some c352, some c431, some c56, some c74, some c327, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 57) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c371, c366, c340, c427, c400, c430, c351, c60, c88, c99, c103, c87, c352, c431, c56, c74, c327] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c427 := derived427 a h
  have h4 : Entails.eval a c400 := derived400 a h
  have h5 : Entails.eval a c430 := derived430 a h
  have h6 : Entails.eval a c351 := h 350 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c431 := derived431 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c262, some c60, some c46, some c327, some c263, some c56, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 57) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c351, c262, c60, c46, c327, c263, c56] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c433, some c73, some c55, some c82, some c324, some c353, some c60, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 57) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c433, c73, c55, c82, c324, c353, c60] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c371, some c366, some c72, some c340, some c432, some c35, some c90, some c405, some c412, some c106, some c434, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 57) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c400, c371, c366, c72, c340, c432, c35, c90, c405, c412, c106, c434] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c340 := h 339 (by decide)
  have h5 : Entails.eval a c432 := derived432 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c405 := derived405 a h
  have h9 : Entails.eval a c412 := derived412 a h
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c434 := derived434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c281, some c295, some c297, some c46, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 57) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c280, c281, c295, c297, c46] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c297 := h 296 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨56, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c434, some c38, some c74, some c263, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 57) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c434, c38, c74, c263] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c434 := derived434 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c436, some c437, some c341, some c355, some c357, some c82, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 57) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c436, c437, c341, c355, c357, c82] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c436 := derived436 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c341 := h 340 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c435, some c438, some c427, some c71, some c341, some c101, some c355, some c357, some c73, some c55, some c323, some c324, some c59, some c207, some c307, some c69, some c22, some c332, some c201, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 57) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c366, c371, c400, c435, c438, c427, c71, c341, c101, c355, c357, c73, c55, c323, c324, c59, c207, c307, c69, c22, c332, c201] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c435 := derived435 a h
  have h4 : Entails.eval a c438 := derived438 a h
  have h5 : Entails.eval a c427 := derived427 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  have h18 : Entails.eval a c69 := h 68 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c332 := h 331 (by decide)
  have h21 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨20, by decide⟩, false), (⟨36, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c22, some c69, some c332, some c337, some c208, some c63, some c25, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 57) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c101, c22, c69, c332, c337, c208, c63, c25] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c90, some c106, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 57) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c89, c90, c106] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨44, by decide⟩, true), (⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c60, some c69, some c351, some c329, some c73, some c59, some c207, some c307, some c230, some c440, some c216, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 57) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c101, c60, c69, c351, c329, c73, c59, c207, c307, c230, c440, c216] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c230 := h 229 (by decide)
  have h10 : Entails.eval a c440 := derived440 a h
  have h11 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c259, some c51, some c292, some c298, some c280, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 57) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c259, c51, c292, c298, c280] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c441, some c2, some c171, some c170, some c187, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 57) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c441, c2, c171, c170, c187] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c441 := derived441 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨40, by decide⟩, false), (⟨44, by decide⟩, true), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c366, some c134, some c443, some c307, some c329, some c65, some c323, some c383, some c390, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 57) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c371, c366, c134, c443, c307, c329, c65, c323, c383, c390] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c443 := derived443 a h
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c383 := derived383 a h
  have h9 : Entails.eval a c390 := derived390 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c435, some c438, some c444, some c441, some c101, some c439, some c427, some c442, some c445, some c327, some c204, some c307, some c233, some c329, some c122, some c58, some c161, some c155, some c170, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 57) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c366, c371, c400, c435, c438, c444, c441, c101, c439, c427, c442, c445, c327, c204, c307, c233, c329, c122, c58, c161, c155, c170] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c435 := derived435 a h
  have h4 : Entails.eval a c438 := derived438 a h
  have h5 : Entails.eval a c444 := derived444 a h
  have h6 : Entails.eval a c441 := derived441 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c439 := derived439 a h
  have h9 : Entails.eval a c427 := derived427 a h
  have h10 : Entails.eval a c442 := derived442 a h
  have h11 : Entails.eval a c445 := derived445 a h
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c233 := h 232 (by decide)
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c122 := h 121 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c155 := h 154 (by decide)
  have h21 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c435, some c400, some c371, some c366, some c438, some c439, some c441, some c101, some c446, some c352, some c353, some c87, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 57) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c435, c400, c371, c366, c438, c439, c441, c101, c446, c352, c353, c87] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c435 := derived435 a h
  have h1 : Entails.eval a c400 := derived400 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c438 := derived438 a h
  have h5 : Entails.eval a c439 := derived439 a h
  have h6 : Entails.eval a c441 := derived441 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c446 := derived446 a h
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨42, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c412, some c99, some c59, some c329, some c58, some c358, some c88, some c351, some c429, some c36, some c270, some c51, some c266, some c131, some c281, some c1, some c155, some c295, some c143, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 57) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c366, c371, c412, c99, c59, c329, c58, c358, c88, c351, c429, c36, c270, c51, c266, c131, c281, c1, c155, c295, c143] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c351 := h 350 (by decide)
  have h10 : Entails.eval a c429 := derived429 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c281 := h 280 (by decide)
  have h17 : Entails.eval a c1 := h 0 (by decide)
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c295 := h 294 (by decide)
  have h20 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨42, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c412, some c99, some c59, some c329, some c88, some c444, some c101, some c58, some c358, some c448, some c341, some c355, some c419, some c429, some c36, some c270, some c269, some c296, some c51, some c39, some c135, some c281, some c11, some c293, some c142, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 57) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c366, c371, c412, c99, c59, c329, c88, c444, c101, c58, c358, c448, c341, c355, c419, c429, c36, c270, c269, c296, c51, c39, c135, c281, c11, c293, c142] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c444 := derived444 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c448 := derived448 a h
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c419 := derived419 a h
  have h15 : Entails.eval a c429 := derived429 a h
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c296 := h 295 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c39 := h 38 (by decide)
  have h22 : Entails.eval a c135 := h 134 (by decide)
  have h23 : Entails.eval a c281 := h 280 (by decide)
  have h24 : Entails.eval a c11 := h 10 (by decide)
  have h25 : Entails.eval a c293 := h 292 (by decide)
  have h26 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c427, some c400, some c371, some c366, some c435, some c447, some c412, some c99, some c88, some c449, some c84, some c353, some c357, some c341, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 57) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c427, c400, c371, c366, c435, c447, c412, c99, c88, c449, c84, c353, c357, c341] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c427 := derived427 a h
  have h1 : Entails.eval a c400 := derived400 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c435 := derived435 a h
  have h5 : Entails.eval a c447 := derived447 a h
  have h6 : Entails.eval a c412 := derived412 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c449 := derived449 a h
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c412, some c100, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 57) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c412, c100] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c412 := derived412 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c452 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c450, some c451, some c102, some c436, some c357, some c358, some c341, some c263, some c46, some c38, some c262, some c415, some c73, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 57) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c366, c371, c400, c450, c451, c102, c436, c357, c358, c341, c263, c46, c38, c262, c415, c73] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c450 := derived450 a h
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c436 := derived436 a h
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c415 := derived415 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c450, some c451, some c102, some c436, some c427, some c452, some c82, some c84, some c56, some c74, some c355, some c103, some c326, some c341, some c58, some c262, some c264, some c47, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 57) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c366, c371, c400, c450, c451, c102, c436, c427, c452, c82, c84, c56, c74, c355, c103, c326, c341, c58, c262, c264, c47] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c450 := derived450 a h
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c436 := derived436 a h
  have h7 : Entails.eval a c427 := derived427 a h
  have h8 : Entails.eval a c452 := derived452 a h
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c341 := h 340 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c262 := h 261 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c82, some c84, some c56, some c74, some c351, some c103, some c327, some c326, some c304, some c311, some c65, some c335, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 57) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c82, c84, c56, c74, c351, c103, c327, c326, c304, c311, c65, c335] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c326 := h 325 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c450, some c451, some c427, some c102, some c436, some c453, some c340, some c454, some c352, some c263, some c423, some c46, some c262, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 57) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c366, c371, c400, c450, c451, c427, c102, c436, c453, c340, c454, c352, c263, c423, c46, c262] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c450 := derived450 a h
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c427 := derived427 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c436 := derived436 a h
  have h8 : Entails.eval a c453 := derived453 a h
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c454 := derived454 a h
  have h11 : Entails.eval a c352 := h 351 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c423 := derived423 a h
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c441, some c71, some c35, some c352, some c263, some c46, some c262, some c290, some c416, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 57) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c441, c71, c35, c352, c263, c46, c262, c290, c416] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c441 := derived441 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c416 := derived416 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c371, some c400, some c427, some c450, some c451, some c455, some c35, some c71, some c89, some c405, some c441, some c456, some c82, some c84, some c56, some c351, some c262, some c108, some c327, some c326, some c37, some c311, some c65, some c323, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 57) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c366, c371, c400, c427, c450, c451, c455, c35, c71, c89, c405, c441, c456, c82, c84, c56, c351, c262, c108, c327, c326, c37, c311, c65, c323] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c427 := derived427 a h
  have h4 : Entails.eval a c450 := derived450 a h
  have h5 : Entails.eval a c451 := derived451 a h
  have h6 : Entails.eval a c455 := derived455 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c405 := derived405 a h
  have h11 : Entails.eval a c441 := derived441 a h
  have h12 : Entails.eval a c456 := derived456 a h
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c351 := h 350 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c108 := h 107 (by decide)
  have h19 : Entails.eval a c327 := h 326 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c37 := h 36 (by decide)
  have h22 : Entails.eval a c311 := h 310 (by decide)
  have h23 : Entails.eval a c65 := h 64 (by decide)
  have h24 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c35, some c82, some c350, some c262, some c84, some c37, some c46, some c368, some c292, some c89, some c40, some c108, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 57) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c71, c35, c82, c350, c262, c84, c37, c46, c368, c292, c89, c40, c108] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨53, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c35, some c458, some c263, some c456, some c46, some c368, some c262, some c73, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 57) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c71, c35, c458, c263, c456, c46, c368, c262, c73] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c458 := derived458 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c456 := derived456 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c37, some c262, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 57) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c73, c37, c262] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c457, some c35, some c71, some c460, some c368, some c372, some c441, some c459, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 57) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c457, c35, c71, c460, c368, c372, c441, c459] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c457 := derived457 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c460 := derived460 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c441 := derived441 a h
  have h7 : Entails.eval a c459 := derived459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c262, some c46, some c263, some c292, some c84, some c40, some c103, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 57) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c350, c262, c46, c263, c292, c84, c40, c103] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c460, some c372, some c457, some c437, some c462, some c82, some c352, some c346, some c423, some c357, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 57) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c460, c372, c457, c437, c462, c82, c352, c346, c423, c357] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c460 := derived460 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c457 := derived457 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c462 := derived462 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c423 := derived423 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c457, some c463, some c101, some c40, some c76, some c264, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 57) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c457, c463, c101, c40, c76, c264] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c457 := derived457 a h
  have h1 : Entails.eval a c463 := derived463 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨50, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c93, some c40, some c76, some c372, some c270, some c95, some c72, some c106, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 57) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c101, c93, c40, c76, c372, c270, c95, c72, c106] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c465, some c436, some c372, some c373, some c92, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 57) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c280, c465, c436, c372, c373, c92] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c465 := derived465 a h
  have h2 : Entails.eval a c436 := derived436 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c461, some c457, some c464, some c131, some c466, some c368, some c73, some c93, some c153, some c3, some c174, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 57) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c461, c457, c464, c131, c466, c368, c73, c93, c153, c3, c174] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c461 := derived461 a h
  have h1 : Entails.eval a c457 := derived457 a h
  have h2 : Entails.eval a c464 := derived464 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c466 := derived466 a h
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c467, some c461, some c457, some c466, some c368, some c73, some c37, some c93, some c101, some c92, some c369, some c281, some c341, some c272, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 57) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c467, c461, c457, c466, c368, c73, c37, c93, c101, c92, c369, c281, c341, c272] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c467 := derived467 a h
  have h1 : Entails.eval a c461 := derived461 a h
  have h2 : Entails.eval a c457 := derived457 a h
  have h3 : Entails.eval a c466 := derived466 a h
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c73, some c37, some c93, some c290, some c103, some c101, some c48, some c92, some c292, some c369, some c286, some c341, some c272, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 57) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c368, c73, c37, c93, c290, c103, c101, c48, c92, c292, c369, c286, c341, c272] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c93, some c355, some c101, some c341, some c92, some c373, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 57) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c73, c93, c355, c101, c341, c92, c373] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c457, some c461, some c467, some c468, some c469, some c340, some c470, some c372, some c341, some c357, some c355, some c82, some c101, some c465, some c95, some c36, some c106, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 57) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c457, c461, c467, c468, c469, c340, c470, c372, c341, c357, c355, c82, c101, c465, c95, c36, c106] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c457 := derived457 a h
  have h1 : Entails.eval a c461 := derived461 a h
  have h2 : Entails.eval a c467 := derived467 a h
  have h3 : Entails.eval a c468 := derived468 a h
  have h4 : Entails.eval a c469 := derived469 a h
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c470 := derived470 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c341 := h 340 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c465 := derived465 a h
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c72, some c267, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 57) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c36, c72, c267] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨51, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c73, some c355, some c267, some c43, some c460, some c291, some c80, some c45, some c110, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 57) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c37, c73, c355, c267, c43, c460, c291, c80, c45, c110] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c460 := derived460 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived473

end CochromaticTwenty.Certificates.B16_6_1
