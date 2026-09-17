import MerLeanExperiment.Certificates.B16_8_2.Steps0000_0099

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c481 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨17, by decide⟩, true), (⟨42, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c453, some c478, some c477, some c480, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 57) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c453, c478, c477, c480] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c453 := derived453 a h
  have h1 : Entails.eval a c478 := derived478 a h
  have h2 : Entails.eval a c477 := derived477 a h
  have h3 : Entails.eval a c480 := derived480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨18, by decide⟩, false), (⟨31, by decide⟩, false), (⟨17, by decide⟩, true), (⟨42, by decide⟩, false), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c339, some c352, some c271, some c305, some c312, some c189, some c198, some c460, some c225, some c84, some c67, some c369, some c103, some c80, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 57) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c339, c352, c271, c305, c312, c189, c198, c460, c225, c84, c67, c369, c103, c80] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c460 := derived460 a h
  have h8 : Entails.eval a c225 := h 224 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c375, some c452, some c453, some c456, some c344, some c465, some c196, some c251, some c475, some c66, some c85, some c20, some c478, some c481, some c463, some c482, some c267, some c312, some c271, some c345, some c210, some c211, some c256, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 57) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c378, c375, c452, c453, c456, c344, c465, c196, c251, c475, c66, c85, c20, c478, c481, c463, c482, c267, c312, c271, c345, c210, c211, c256] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c452 := derived452 a h
  have h3 : Entails.eval a c453 := derived453 a h
  have h4 : Entails.eval a c456 := derived456 a h
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c465 := derived465 a h
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c475 := derived475 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c478 := derived478 a h
  have h14 : Entails.eval a c481 := derived481 a h
  have h15 : Entails.eval a c463 := derived463 a h
  have h16 : Entails.eval a c482 := derived482 a h
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c211 := h 210 (by decide)
  have h23 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨43, by decide⟩, false), (⟨37, by decide⟩, true), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c271, some c24, some c282, some c201, some c356, some c277, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 57) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c196, c271, c24, c282, c201, c356, c277] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c86, some c378, some c85, some c65, some c437, some c344, some c339, some c59, some c35, some c54, some c453, some c299, some c345, some c58, some c314, some c78, some c484, some c303, some c208, some c251, some c215, some c219, some c230, some c356, some c277, some c225, some c201, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 57) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c375, c86, c378, c85, c65, c437, c344, c339, c59, c35, c54, c453, c299, c345, c58, c314, c78, c484, c303, c208, c251, c215, c219, c230, c356, c277, c225, c201] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c437 := derived437 a h
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c453 := derived453 a h
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c484 := derived484 a h
  have h18 : Entails.eval a c303 := h 302 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c251 := h 250 (by decide)
  have h21 : Entails.eval a c215 := h 214 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c230 := h 229 (by decide)
  have h24 : Entails.eval a c356 := h 355 (by decide)
  have h25 : Entails.eval a c277 := h 276 (by decide)
  have h26 : Entails.eval a c225 := h 224 (by decide)
  have h27 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨29, by decide⟩, true), (⟨35, by decide⟩, false), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c271, some c24, some c322, some c213, some c356, some c317, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 57) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c196, c271, c24, c322, c213, c356, c317] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c375, some c483, some c97, some c104, some c65, some c85, some c86, some c485, some c195, some c304, some c299, some c47, some c35, some c42, some c453, some c305, some c46, some c274, some c78, some c486, some c343, some c397, some c203, some c207, some c230, some c356, some c225, some c317, some c213, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 57) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c437, c378, c375, c483, c97, c104, c65, c85, c86, c485, c195, c304, c299, c47, c35, c42, c453, c305, c46, c274, c78, c486, c343, c397, c203, c207, c230, c356, c225, c317, c213] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c483 := derived483 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c485 := derived485 a h
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c453 := derived453 a h
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c46 := h 45 (by decide)
  have h19 : Entails.eval a c274 := h 273 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c486 := derived486 a h
  have h22 : Entails.eval a c343 := h 342 (by decide)
  have h23 : Entails.eval a c397 := derived397 a h
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c207 := h 206 (by decide)
  have h26 : Entails.eval a c230 := h 229 (by decide)
  have h27 : Entails.eval a c356 := h 355 (by decide)
  have h28 : Entails.eval a c225 := h 224 (by decide)
  have h29 : Entails.eval a c317 := h 316 (by decide)
  have h30 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨6, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c487, some c252, some c375, some c64, some c38, some c97, some c104, some c30, some c303, some c86, some c58, some c207, some c247, some c203, some c299, some c311, some c268, some c205, some c351, some c348, some c218, some c212, some c257, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 57) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c487, c252, c375, c64, c38, c97, c104, c30, c303, c86, c58, c207, c247, c203, c299, c311, c268, c205, c351, c348, c218, c212, c257] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c487 := derived487 a h
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  have h15 : Entails.eval a c311 := h 310 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c205 := h 204 (by decide)
  have h18 : Entails.eval a c351 := h 350 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c487, some c252, some c375, some c488, some c343, some c196, some c303, some c304, some c465, some c97, some c104, some c30, some c86, some c46, some c219, some c247, some c215, some c351, some c268, some c217, some c308, some c311, some c200, some c206, some c257, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 57) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c487, c252, c375, c488, c343, c196, c303, c304, c465, c97, c104, c30, c86, c46, c219, c247, c215, c351, c268, c217, c308, c311, c200, c206, c257] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c487 := derived487 a h
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c488 := derived488 a h
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c465 := derived465 a h
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c219 := h 218 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c215 := h 214 (by decide)
  have h17 : Entails.eval a c351 := h 350 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c217 := h 216 (by decide)
  have h20 : Entails.eval a c308 := h 307 (by decide)
  have h21 : Entails.eval a c311 := h 310 (by decide)
  have h22 : Entails.eval a c200 := h 199 (by decide)
  have h23 : Entails.eval a c206 := h 205 (by decide)
  have h24 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c453, some c252, some c40, some c304, some c39, some c97, some c30, some c412, some c85, some c219, some c351, some c101, some c61, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 57) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c375, c453, c252, c40, c304, c39, c97, c30, c412, c85, c219, c351, c101, c61] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c412 := derived412 a h
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c351 := h 350 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c303, some c304, some c272, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 57) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c303, c304, c272] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c303 := h 302 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c453, some c97, some c30, some c404, some c85, some c207, some c101, some c311, some c49, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 57) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c453, c97, c30, c404, c85, c207, c101, c311, c49] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c453 := derived453 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨30, by decide⟩, true), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨32, by decide⟩, true), (⟨38, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c207, some c311, some c266, some c351, some c348, some c212, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 57) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c207, c311, c266, c351, c348, c212] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c453, some c85, some c101, some c60, some c49, some c87, some c301, some c194, some c23, some c249, some c493, some c253, some c260, some c203, some c312, some c308, some c270, some c190, some c351, some c450, some c210, some c169, some c172, some c133, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 57) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c39, c453, c85, c101, c60, c49, c87, c301, c194, c23, c249, c493, c253, c260, c203, c312, c308, c270, c190, c351, c450, c210, c169, c172, c133] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c249 := h 248 (by decide)
  have h11 : Entails.eval a c493 := derived493 a h
  have h12 : Entails.eval a c253 := h 252 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c312 := h 311 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c351 := h 350 (by decide)
  have h20 : Entails.eval a c450 := derived450 a h
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c169 := h 168 (by decide)
  have h23 : Entails.eval a c172 := h 171 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c172, some c1, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 57) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c169, c172, c1] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c348, some c140, some c450, some c214, some c111, some c249, some c5, some c68, some c67, some c281, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 57) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c348, c140, c450, c214, c111, c249, c5, c68, c67, c281] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c348 := h 347 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c450 := derived450 a h
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c203, some c312, some c101, some c60, some c49, some c308, some c496, some c190, some c264, some c23, some c351, some c214, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c39, c203, c312, c101, c60, c49, c308, c496, c190, c264, c23, c351, c214] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c496 := derived496 a h
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c351 := h 350 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c203, some c299, some c497, some c66, some c57, some c320, some c140, some c111, some c137, some c184, some c214, some c113, some c165, some c29, some c318, some c60, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c39, c203, c299, c497, c66, c57, c320, c140, c111, c137, c184, c214, c113, c165, c29, c318, c60] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c318 := h 317 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c10, some c170, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c1, c10, c170] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c487, some c252, some c437, some c378, some c375, some c489, some c453, some c490, some c343, some c491, some c492, some c39, some c494, some c495, some c498, some c247, some c260, some c207, some c312, some c47, some c103, some c49, some c499, some c153, some c284, some c286, some c80, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c487, c252, c437, c378, c375, c489, c453, c490, c343, c491, c492, c39, c494, c495, c498, c247, c260, c207, c312, c47, c103, c49, c499, c153, c284, c286, c80] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c487 := derived487 a h
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c489 := derived489 a h
  have h6 : Entails.eval a c453 := derived453 a h
  have h7 : Entails.eval a c490 := derived490 a h
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c491 := derived491 a h
  have h10 : Entails.eval a c492 := derived492 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c494 := derived494 a h
  have h13 : Entails.eval a c495 := derived495 a h
  have h14 : Entails.eval a c498 := derived498 a h
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c260 := h 259 (by decide)
  have h17 : Entails.eval a c207 := h 206 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c103 := h 102 (by decide)
  have h21 : Entails.eval a c49 := h 48 (by decide)
  have h22 : Entails.eval a c499 := derived499 a h
  have h23 : Entails.eval a c153 := h 152 (by decide)
  have h24 : Entails.eval a c284 := h 283 (by decide)
  have h25 : Entails.eval a c286 := h 285 (by decide)
  have h26 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨38, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c219, some c352, some c59, some c266, some c215, some c103, some c48, some c308, some c311, some c45, some c200, some c21, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c219, c352, c59, c266, c215, c103, c48, c308, c311, c45, c200, c21] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c48, some c101, some c103, some c66, some c45, some c67, some c277, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c311, c48, c101, c103, c66, c45, c67, c277] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨43, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c196, some c29, some c101, some c217, some c66, some c45, some c321, some c280, some c124, some c165, some c111, some c141, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c215, c196, c29, c101, c217, c66, c45, c321, c280, c124, c165, c111, c141] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c323, some c503, some c61, some c80, some c321, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c215, c323, c503, c61, c80, c321] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c503 := derived503 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨51, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c502, some c453, some c495, some c18, some c198, some c504, some c67, some c354, some c499, some c273, some c153, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c502, c453, c495, c18, c198, c504, c67, c354, c499, c273, c153] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c502 := derived502 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c495 := derived495 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c504 := derived504 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c499 := derived499 a h
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨38, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c453, some c194, some c196, some c501, some c260, some c215, some c339, some c352, some c270, some c502, some c505, some c253, some c86, some c198, some c65, some c85, some c103, some c276, some c273, some c23, some c61, some c48, some c81, some c356, some c348, some c278, some c190, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c38, c453, c194, c196, c501, c260, c215, c339, c352, c270, c502, c505, c253, c86, c198, c65, c85, c103, c276, c273, c23, c61, c48, c81, c356, c348, c278, c190] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c501 := derived501 a h
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c502 := derived502 a h
  have h11 : Entails.eval a c505 := derived505 a h
  have h12 : Entails.eval a c253 := h 252 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c85 := h 84 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  have h19 : Entails.eval a c273 := h 272 (by decide)
  have h20 : Entails.eval a c23 := h 22 (by decide)
  have h21 : Entails.eval a c61 := h 60 (by decide)
  have h22 : Entails.eval a c48 := h 47 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c356 := h 355 (by decide)
  have h25 : Entails.eval a c348 := h 347 (by decide)
  have h26 : Entails.eval a c278 := h 277 (by decide)
  have h27 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c453, some c506, some c97, some c104, some c412, some c86, some c339, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c38, c453, c506, c97, c104, c412, c86, c339] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c506 := derived506 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c412 := derived412 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c104, some c412, some c86, some c339, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c97, c104, c412, c86, c339] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c412 := derived412 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨37, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c277, some c264, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c317, c277, c264] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c453, some c508, some c59, some c339, some c352, some c86, some c67, some c219, some c495, some c323, some c260, some c504, some c202, some c502, some c509, some c66, some c356, some c101, some c371, some c80, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c453, c508, c59, c339, c352, c86, c67, c219, c495, c323, c260, c504, c202, c502, c509, c66, c356, c101, c371, c80] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c453 := derived453 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c495 := derived495 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c504 := derived504 a h
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c502 := derived502 a h
  have h14 : Entails.eval a c509 := derived509 a h
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c371 := h 370 (by decide)
  have h19 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨10, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c48, some c196, some c339, some c352, some c321, some c499, some c219, some c151, some c153, some c5, some c232, some c45, some c439, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c103, c48, c196, c339, c352, c321, c499, c219, c151, c153, c5, c232, c45, c439] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c499 := derived499 a h
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c507, some c453, some c508, some c510, some c103, some c61, some c341, some c87, some c68, some c495, some c511, some c215, some c247, some c260, some c499, some c219, some c153, some c324, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c507, c453, c508, c510, c103, c61, c341, c87, c68, c495, c511, c215, c247, c260, c499, c219, c153, c324] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c507 := derived507 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c510 := derived510 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c495 := derived495 a h
  have h10 : Entails.eval a c511 := derived511 a h
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c499 := derived499 a h
  have h15 : Entails.eval a c219 := h 218 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c375, some c487, some c252, some c500, some c344, some c196, some c303, some c304, some c512, some c465, some c97, some c104, some c86, some c247, some c339, some c215, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c437, c378, c375, c487, c252, c500, c344, c196, c303, c304, c512, c465, c97, c104, c86, c247, c339, c215] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c487 := derived487 a h
  have h4 : Entails.eval a c252 := h 251 (by decide)
  have h5 : Entails.eval a c500 := derived500 a h
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c512 := derived512 a h
  have h11 : Entails.eval a c465 := derived465 a h
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c339 := h 338 (by decide)
  have h17 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c375, some c59, some c99, some c485, some c86, some c252, some c247, some c215, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 57) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c344, c375, c59, c99, c485, c86, c252, c247, c215] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c485 := derived485 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c513, some c375, some c514, some c339, some c352, some c86, some c63, some c99, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 57) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c344, c513, c375, c514, c339, c352, c86, c63, c99] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c513 := derived513 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c514 := derived514 a h
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨25, by decide⟩, true), (⟨37, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c27, some c219, some c198, some c253, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 57) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c252, c27, c219, c198, c253] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c217, some c304, some c249, some c208, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 57) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c196, c217, c304, c249, c208] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c249 := h 248 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨34, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨3, by decide⟩, false), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c139, some c170, some c116, some c135, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 57) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c5, c139, c170, c116, c135] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c109, some c135, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c169, c109, c135] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c513, some c88, some c515, some c100, some c344, some c69, some c375, some c339, some c352, some c37, some c63, some c62, some c99, some c65, some c410, some c273, some c341, some c33, some c43, some c311, some c301, some c516, some c517, some c251, some c24, some c202, some c519, some c5, some c518, some c151, some c212, some c230, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c437, c378, c513, c88, c515, c100, c344, c69, c375, c339, c352, c37, c63, c62, c99, c65, c410, c273, c341, c33, c43, c311, c301, c516, c517, c251, c24, c202, c519, c5, c518, c151, c212, c230] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c515 := derived515 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c352 := h 351 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c410 := derived410 a h
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c311 := h 310 (by decide)
  have h22 : Entails.eval a c301 := h 300 (by decide)
  have h23 : Entails.eval a c516 := derived516 a h
  have h24 : Entails.eval a c517 := derived517 a h
  have h25 : Entails.eval a c251 := h 250 (by decide)
  have h26 : Entails.eval a c24 := h 23 (by decide)
  have h27 : Entails.eval a c202 := h 201 (by decide)
  have h28 : Entails.eval a c519 := derived519 a h
  have h29 : Entails.eval a c5 := h 4 (by decide)
  have h30 : Entails.eval a c518 := derived518 a h
  have h31 : Entails.eval a c151 := h 150 (by decide)
  have h32 : Entails.eval a c212 := h 211 (by decide)
  have h33 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c513, some c88, some c100, some c69, some c375, some c37, some c63, some c62, some c99, some c65, some c87, some c273, some c341, some c43, some c311, some c301, some c267, some c516, some c304, some c517, some c208, some c251, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c437, c378, c513, c88, c100, c69, c375, c37, c63, c62, c99, c65, c87, c273, c341, c43, c311, c301, c267, c516, c304, c517, c208, c251] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c273 := h 272 (by decide)
  have h14 : Entails.eval a c341 := h 340 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c311 := h 310 (by decide)
  have h17 : Entails.eval a c301 := h 300 (by decide)
  have h18 : Entails.eval a c267 := h 266 (by decide)
  have h19 : Entails.eval a c516 := derived516 a h
  have h20 : Entails.eval a c304 := h 303 (by decide)
  have h21 : Entails.eval a c517 := derived517 a h
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c303, some c304, some c208, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c303, c304, c208] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c303 := h 302 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨51, by decide⟩, true), (⟨21, by decide⟩, true), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c123, some c170, some c114, some c116, some c181, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c5, c123, c170, c114, c116, c181] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c172, some c109, some c181, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c169, c172, c109, c181] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c151, some c230, some c200, some c523, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c5, c151, c230, c200, c523] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c523 := derived523 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨23, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c513, some c88, some c100, some c69, some c375, some c251, some c522, some c40, some c267, some c99, some c24, some c65, some c87, some c33, some c55, some c273, some c341, some c50, some c214, some c301, some c524, some c525, some c299, some c245, some c204, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c437, c378, c513, c88, c100, c69, c375, c251, c522, c40, c267, c99, c24, c65, c87, c33, c55, c273, c341, c50, c214, c301, c524, c525, c299, c245, c204] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c522 := derived522 a h
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c55 := h 54 (by decide)
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c50 := h 49 (by decide)
  have h20 : Entails.eval a c214 := h 213 (by decide)
  have h21 : Entails.eval a c301 := h 300 (by decide)
  have h22 : Entails.eval a c524 := derived524 a h
  have h23 : Entails.eval a c525 := derived525 a h
  have h24 : Entails.eval a c299 := h 298 (by decide)
  have h25 : Entails.eval a c245 := h 244 (by decide)
  have h26 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨33, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c33, some c273, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c65, c33, c273] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c38, some c527, some c99, some c61, some c341, some c324, some c68, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c50, c38, c527, c99, c61, c341, c324, c68] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c527 := derived527 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c437, some c378, some c513, some c88, some c69, some c375, some c515, some c100, some c520, some c521, some c345, some c528, some c303, some c196, some c252, some c526, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c344, c437, c378, c513, c88, c69, c375, c515, c100, c520, c521, c345, c528, c303, c196, c252, c526] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c520 := derived520 a h
  have h10 : Entails.eval a c521 := derived521 a h
  have h11 : Entails.eval a c345 := h 344 (by decide)
  have h12 : Entails.eval a c528 := derived528 a h
  have h13 : Entails.eval a c303 := h 302 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c526 := derived526 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c324, some c269, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c285, c324, c269] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c324 := h 323 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c326, some c84, some c530, some c80, some c100, some c6, some c58, some c152, some c341, some c301, some c269, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c352, c326, c84, c530, c80, c100, c6, c58, c152, c341, c301, c269] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c530 := derived530 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c301, some c152, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c284, c301, c152] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨38, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c6, some c532, some c269, some c341, some c152, some c371, some c325, some c78, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c100, c6, c532, c269, c341, c152, c371, c325, c78] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c532 := derived532 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c341, some c349, some c87, some c68, some c212, some c20, some c284, some c232, some c48, some c199, some c305, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c341, c349, c87, c68, c212, c20, c284, c232, c48, c199, c305] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c341 := h 340 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c40, some c24, some c531, some c37, some c62, some c533, some c534, some c269, some c284, some c301, some c68, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c196, c40, c24, c531, c37, c62, c533, c534, c269, c284, c301, c68] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c531 := derived531 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c533 := derived533 a h
  have h7 : Entails.eval a c534 := derived534 a h
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c437, some c378, some c513, some c88, some c69, some c375, some c529, some c465, some c196, some c40, some c251, some c252, some c24, some c524, some c535, some c50, some c38, some c208, some c312, some c305, some c46, some c267, some c100, some c339, some c352, some c534, some c461, some c269, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c344, c437, c378, c513, c88, c69, c375, c529, c465, c196, c40, c251, c252, c24, c524, c535, c50, c38, c208, c312, c305, c46, c267, c100, c339, c352, c534, c461, c269] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c529 := derived529 a h
  have h8 : Entails.eval a c465 := derived465 a h
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c524 := derived524 a h
  have h15 : Entails.eval a c535 := derived535 a h
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c38 := h 37 (by decide)
  have h18 : Entails.eval a c208 := h 207 (by decide)
  have h19 : Entails.eval a c312 := h 311 (by decide)
  have h20 : Entails.eval a c305 := h 304 (by decide)
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c267 := h 266 (by decide)
  have h23 : Entails.eval a c100 := h 99 (by decide)
  have h24 : Entails.eval a c339 := h 338 (by decide)
  have h25 : Entails.eval a c352 := h 351 (by decide)
  have h26 : Entails.eval a c534 := derived534 a h
  have h27 : Entails.eval a c461 := derived461 a h
  have h28 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c513, some c88, some c69, some c375, some c344, some c536, some c453, some c101, some c63, some c40, some c61, some c352, some c326, some c303, some c304, some c324, some c80, some c68, some c341, some c194, some c251, some c23, some c249, some c412, some c524, some c201, some c204, some c439, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c437, c378, c513, c88, c69, c375, c344, c536, c453, c101, c63, c40, c61, c352, c326, c303, c304, c324, c80, c68, c341, c194, c251, c23, c249, c412, c524, c201, c204, c439] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c536 := derived536 a h
  have h8 : Entails.eval a c453 := derived453 a h
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c326 := h 325 (by decide)
  have h15 : Entails.eval a c303 := h 302 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c324 := h 323 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c341 := h 340 (by decide)
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c251 := h 250 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  have h24 : Entails.eval a c249 := h 248 (by decide)
  have h25 : Entails.eval a c412 := derived412 a h
  have h26 : Entails.eval a c524 := derived524 a h
  have h27 : Entails.eval a c201 := h 200 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c341, some c68, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c324, c341, c68] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨30, by decide⟩, true), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c538, some c61, some c453, some c99, some c528, some c65, some c313, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c538, c61, c453, c99, c528, c65, c313] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c538 := derived538 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c528 := derived528 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c437, some c378, some c513, some c88, some c69, some c375, some c304, some c491, some c39, some c195, some c252, some c539, some c101, some c100, some c50, some c46, some c282, some c311, some c67, some c268, some c247, some c351, some c215, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c537, c437, c378, c513, c88, c69, c375, c304, c491, c39, c195, c252, c539, c101, c100, c50, c46, c282, c311, c67, c268, c247, c351, c215] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c491 := derived491 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c539 := derived539 a h
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c46 := h 45 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c311 := h 310 (by decide)
  have h19 : Entails.eval a c67 := h 66 (by decide)
  have h20 : Entails.eval a c268 := h 267 (by decide)
  have h21 : Entails.eval a c247 := h 246 (by decide)
  have h22 : Entails.eval a c351 := h 350 (by decide)
  have h23 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨37, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c437, some c378, some c513, some c88, some c69, some c375, some c540, some c196, some c40, some c251, some c252, some c397, some c453, some c24, some c208, some c50, some c213, some c312, some c349, some c46, some c100, some c60, some c539, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c537, c437, c378, c513, c88, c69, c375, c540, c196, c40, c251, c252, c397, c453, c24, c208, c50, c213, c312, c349, c46, c100, c60, c539] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c397 := derived397 a h
  have h13 : Entails.eval a c453 := derived453 a h
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c46 := h 45 (by decide)
  have h21 : Entails.eval a c100 := h 99 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c539 := derived539 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c437, some c378, some c513, some c88, some c69, some c375, some c541, some c343, some c397, some c38, some c491, some c272, some c453, some c101, some c49, some c51, some c312, some c286, some c284, some c47, some c203, some c266, some c80, some c68, some c27, some c351, some c398, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c537, c437, c378, c513, c88, c69, c375, c541, c343, c397, c38, c491, c272, c453, c101, c49, c51, c312, c286, c284, c47, c203, c266, c80, c68, c27, c351, c398] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c541 := derived541 a h
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c397 := derived397 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c491 := derived491 a h
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c453 := derived453 a h
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c51 := h 50 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c286 := h 285 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c203 := h 202 (by decide)
  have h22 : Entails.eval a c266 := h 265 (by decide)
  have h23 : Entails.eval a c80 := h 79 (by decide)
  have h24 : Entails.eval a c68 := h 67 (by decide)
  have h25 : Entails.eval a c27 := h 26 (by decide)
  have h26 : Entails.eval a c351 := h 350 (by decide)
  have h27 : Entails.eval a c398 := derived398 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, false), (⟨36, by decide⟩, true), (⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c513, some c378, some c375, some c397, some c62, some c398, some c453, some c404, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c537, c513, c378, c375, c397, c62, c398, c453, c404] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c513 := derived513 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c397 := derived397 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c398 := derived398 a h
  have h7 : Entails.eval a c453 := derived453 a h
  have h8 : Entails.eval a c404 := derived404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c513, some c542, some c37, some c537, some c437, some c378, some c88, some c69, some c375, some c36, some c60, some c311, some c284, some c68, some c543, some c343, some c63, some c196, some c24, some c251, some c252, some c202, some c208, some c213, some c524, some c216, some c139, some c259, some c116, some c114, some c130, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c513, c542, c37, c537, c437, c378, c88, c69, c375, c36, c60, c311, c284, c68, c543, c343, c63, c196, c24, c251, c252, c202, c208, c213, c524, c216, c139, c259, c116, c114, c130] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c513 := derived513 a h
  have h1 : Entails.eval a c542 := derived542 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c537 := derived537 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c543 := derived543 a h
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c196 := h 195 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c251 := h 250 (by decide)
  have h20 : Entails.eval a c252 := h 251 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c213 := h 212 (by decide)
  have h24 : Entails.eval a c524 := derived524 a h
  have h25 : Entails.eval a c216 := h 215 (by decide)
  have h26 : Entails.eval a c139 := h 138 (by decide)
  have h27 : Entails.eval a c259 := h 258 (by decide)
  have h28 : Entails.eval a c116 := h 115 (by decide)
  have h29 : Entails.eval a c114 := h 113 (by decide)
  have h30 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c343, some c341, some c63, some c196, some c87, some c24, some c99, some c534, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c37, c343, c341, c63, c196, c87, c24, c99, c534] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c341 := h 340 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c534 := derived534 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c513, some c542, some c37, some c537, some c437, some c378, some c88, some c69, some c375, some c544, some c545, some c397, some c62, some c272, some c194, some c453, some c312, some c23, some c49, some c266, some c203, some c493, some c348, some c260, some c213, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c513, c542, c37, c537, c437, c378, c88, c69, c375, c544, c545, c397, c62, c272, c194, c453, c312, c23, c49, c266, c203, c493, c348, c260, c213] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c513 := derived513 a h
  have h1 : Entails.eval a c542 := derived542 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c537 := derived537 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c544 := derived544 a h
  have h10 : Entails.eval a c545 := derived545 a h
  have h11 : Entails.eval a c397 := derived397 a h
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c453 := derived453 a h
  have h16 : Entails.eval a c312 := h 311 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c49 := h 48 (by decide)
  have h19 : Entails.eval a c266 := h 265 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c493 := derived493 a h
  have h22 : Entails.eval a c348 := h 347 (by decide)
  have h23 : Entails.eval a c260 := h 259 (by decide)
  have h24 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c513, some c542, some c37, some c537, some c437, some c378, some c88, some c546, some c101, some c100, some c38, some c46, some c343, some c312, some c196, some c195, some c252, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c513, c542, c37, c537, c437, c378, c88, c546, c101, c100, c38, c46, c343, c312, c196, c195, c252] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c513 := derived513 a h
  have h1 : Entails.eval a c542 := derived542 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c537 := derived537 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c546 := derived546 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c437, some c378, some c513, some c88, some c69, some c375, some c542, some c37, some c547, some c304, some c491, some c39, some c195, some c343, some c252, some c63, some c219, some c453, some c99, some c260, some c253, some c65, some c527, some c273, some c314, some c198, some c311, some c282, some c43, some c78, some c100, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c537, c437, c378, c513, c88, c69, c375, c542, c37, c547, c304, c491, c39, c195, c343, c252, c63, c219, c453, c99, c260, c253, c65, c527, c273, c314, c198, c311, c282, c43, c78, c100] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c437 := derived437 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c542 := derived542 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c547 := derived547 a h
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c491 := derived491 a h
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c453 := derived453 a h
  have h19 : Entails.eval a c99 := h 98 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c253 := h 252 (by decide)
  have h22 : Entails.eval a c65 := h 64 (by decide)
  have h23 : Entails.eval a c527 := derived527 a h
  have h24 : Entails.eval a c273 := h 272 (by decide)
  have h25 : Entails.eval a c314 := h 313 (by decide)
  have h26 : Entails.eval a c198 := h 197 (by decide)
  have h27 : Entails.eval a c311 := h 310 (by decide)
  have h28 : Entails.eval a c282 := h 281 (by decide)
  have h29 : Entails.eval a c43 := h 42 (by decide)
  have h30 : Entails.eval a c78 := h 77 (by decide)
  have h31 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c437, some c378, some c513, some c88, some c101, some c548, some c303, some c537, some c69, some c375, some c343, some c196, some c40, some c252, some c24, some c213, some c524, some c349, some c6, some c533, some c269, some c216, some c301, some c309, some c152, some c200, some c232, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c437, c378, c513, c88, c101, c548, c303, c537, c69, c375, c343, c196, c40, c252, c24, c213, c524, c349, c6, c533, c269, c216, c301, c309, c152, c200, c232] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c437 := derived437 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c513 := derived513 a h
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c548 := derived548 a h
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c537 := derived537 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c213 := h 212 (by decide)
  have h16 : Entails.eval a c524 := derived524 a h
  have h17 : Entails.eval a c349 := h 348 (by decide)
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c533 := derived533 a h
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  have h22 : Entails.eval a c301 := h 300 (by decide)
  have h23 : Entails.eval a c309 := h 308 (by decide)
  have h24 : Entails.eval a c152 := h 151 (by decide)
  have h25 : Entails.eval a c200 := h 199 (by decide)
  have h26 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c274, some c313, some c33, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c65, c274, c313, c33] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c548, some c303, some c537, some c437, some c378, some c513, some c88, some c69, some c375, some c101, some c100, some c549, some c62, some c64, some c58, some c351, some c322, some c78, some c550, some c99, some c418, some c47, some c312, some c311, some c268, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c548, c303, c537, c437, c378, c513, c88, c69, c375, c101, c100, c549, c62, c64, c58, c351, c322, c78, c550, c99, c418, c47, c312, c311, c268] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c548 := derived548 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c537 := derived537 a h
  have h3 : Entails.eval a c437 := derived437 a h
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c513 := derived513 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c549 := derived549 a h
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c322 := h 321 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c550 := derived550 a h
  have h19 : Entails.eval a c99 := h 98 (by decide)
  have h20 : Entails.eval a c418 := derived418 a h
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c312 := h 311 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c284, some c68, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c301, c284, c68] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c43, some c273, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c65, c43, c273] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨38, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨30, by decide⟩, false), (⟨39, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c552, some c49, some c553, some c453, some c99, some c64, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c552, c49, c553, c453, c99, c64] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c553 := derived553 a h
  have h3 : Entails.eval a c453 := derived453 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c551, some c548, some c303, some c537, some c437, some c513, some c69, some c378, some c375, some c397, some c554, some c37, some c207, some c51, some c453, some c64, some c99, some c65, some c87, some c313, some c221, some c301, some c55, some c205, some c351, some c259, some c210, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c551, c548, c303, c537, c437, c513, c69, c378, c375, c397, c554, c37, c207, c51, c453, c64, c99, c65, c87, c313, c221, c301, c55, c205, c351, c259, c210] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c551 := derived551 a h
  have h1 : Entails.eval a c548 := derived548 a h
  have h2 : Entails.eval a c303 := h 302 (by decide)
  have h3 : Entails.eval a c537 := derived537 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c513 := derived513 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c397 := derived397 a h
  have h10 : Entails.eval a c554 := derived554 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c453 := derived453 a h
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c87 := h 86 (by decide)
  have h19 : Entails.eval a c313 := h 312 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c301 := h 300 (by decide)
  have h22 : Entails.eval a c55 := h 54 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c351 := h 350 (by decide)
  have h25 : Entails.eval a c259 := h 258 (by decide)
  have h26 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c378, some c437, some c513, some c88, some c537, some c548, some c303, some c551, some c555, some c343, some c196, some c40, some c252, some c24, some c213, some c349, some c36, some c60, some c301, some c99, some c87, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c375, c378, c437, c513, c88, c537, c548, c303, c551, c555, c343, c196, c40, c252, c24, c213, c349, c36, c60, c301, c99, c87] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c437 := derived437 a h
  have h3 : Entails.eval a c513 := derived513 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c537 := derived537 a h
  have h6 : Entails.eval a c548 := derived548 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c551 := derived551 a h
  have h9 : Entails.eval a c555 := derived555 a h
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c213 := h 212 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c60 := h 59 (by decide)
  have h19 : Entails.eval a c301 := h 300 (by decide)
  have h20 : Entails.eval a c99 := h 98 (by decide)
  have h21 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c314, some c33, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c274, c314, c33] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c314 := h 313 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨52, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c41, some c300, some c273, some c69, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c44, c41, c300, c273, c69] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c250, some c248, some c216, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c250, c248, c216] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c250 := h 249 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c5, some c111, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c8, c5, c111] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c336, some c169, some c133, some c136, some c115, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c336, c169, c133, c136, c115] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c336 := h 335 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c375, some c65, some c558, some c556, some c102, some c94, some c70, some c380, some c300, some c274, some c86, some c37, some c33, some c342, some c340, some c559, some c200, some c24, some c21, some c207, some c304, some c265, some c560, some c561, some c217, some c242, some c257, some c169, some c133, some c115, some c114, some c131, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c309, c375, c65, c558, c556, c102, c94, c70, c380, c300, c274, c86, c37, c33, c342, c340, c559, c200, c24, c21, c207, c304, c265, c560, c561, c217, c242, c257, c169, c133, c115, c114, c131] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c558 := derived558 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c340 := h 339 (by decide)
  have h16 : Entails.eval a c559 := derived559 a h
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c207 := h 206 (by decide)
  have h21 : Entails.eval a c304 := h 303 (by decide)
  have h22 : Entails.eval a c265 := h 264 (by decide)
  have h23 : Entails.eval a c560 := derived560 a h
  have h24 : Entails.eval a c561 := derived561 a h
  have h25 : Entails.eval a c217 := h 216 (by decide)
  have h26 : Entails.eval a c242 := h 241 (by decide)
  have h27 : Entails.eval a c257 := h 256 (by decide)
  have h28 : Entails.eval a c169 := h 168 (by decide)
  have h29 : Entails.eval a c133 := h 132 (by decide)
  have h30 : Entails.eval a c115 := h 114 (by decide)
  have h31 : Entails.eval a c114 := h 113 (by decide)
  have h32 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c366, some c81, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c285, c366, c81] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨18, by decide⟩, false), (⟨50, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c150, some c182, some c111, some c113, some c11, some c226, some c81, some c164, some c367, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c169, c150, c182, c111, c113, c11, c226, c81, c164, c367] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨52, by decide⟩, false), (⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c42, some c297, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c86, c42, c297] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c182, some c113, some c256, some c564, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c169, c182, c113, c256, c564] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c182 := h 181 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c564 := derived564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨41, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c253, some c223, some c200, some c164, some c300, some c284, some c69, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c109, c253, c223, c200, c164, c300, c284, c69] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c129, some c87, some c65, some c309, some c169, some c182, some c118, some c113, some c565, some c566, some c197, some c567, some c11, some c181, some c111, some c108, some c259, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c129, c87, c65, c309, c169, c182, c118, c113, c565, c566, c197, c567, c11, c181, c111, c108, c259] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c129 := h 128 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c565 := derived565 a h
  have h9 : Entails.eval a c566 := derived566 a h
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c567 := derived567 a h
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c181 := h 180 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c108 := h 107 (by decide)
  have h16 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c334, some c336, some c61, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c334, c336, c61] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c334 := h 333 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c129, some c309, some c65, some c87, some c558, some c568, some c376, some c86, some c569, some c190, some c242, some c21, some c113, some c131, some c51, some c203, some c311, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c129, c309, c65, c87, c558, c568, c376, c86, c569, c190, c242, c21, c113, c131, c51, c203, c311] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c129 := h 128 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c558 := derived558 a h
  have h5 : Entails.eval a c568 := derived568 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c569 := derived569 a h
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c242 := h 241 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c244, some c569, some c190, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c244, c569, c190] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c244 := h 243 (by decide)
  have h1 : Entails.eval a c569 := derived569 a h
  have h2 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨50, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c519, some c197, some c220, some c254, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c519, c197, c220, c254] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c519 := derived519 a h
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c556, some c375, some c65, some c87, some c558, some c562, some c563, some c70, some c154, some c7, some c570, some c252, some c571, some c169, some c118, some c33, some c134, some c572, some c258, some c220, some c344, some c345, some c63, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c309, c556, c375, c65, c87, c558, c562, c563, c70, c154, c7, c570, c252, c571, c169, c118, c33, c134, c572, c258, c220, c344, c345, c63] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c558 := derived558 a h
  have h6 : Entails.eval a c562 := derived562 a h
  have h7 : Entails.eval a c563 := derived563 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c570 := derived570 a h
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c571 := derived571 a h
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c33 := h 32 (by decide)
  have h17 : Entails.eval a c134 := h 133 (by decide)
  have h18 : Entails.eval a c572 := derived572 a h
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c220 := h 219 (by decide)
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c345 := h 344 (by decide)
  have h23 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c70, some c300, some c285, some c51, some c81, some c287, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c94, c70, c300, c285, c51, c81, c287] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c44, some c131, some c7, some c169, some c569, some c571, some c190, some c113, some c242, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c51, c44, c131, c7, c169, c569, c571, c190, c113, c242] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c569 := derived569 a h
  have h6 : Entails.eval a c571 := derived571 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c569, some c242, some c190, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c569, c242, c190] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c569 := derived569 a h
  have h1 : Entails.eval a c242 := h 241 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c88, some c7, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c169, c88, c7] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c309, some c129, some c2, some c575, some c300, some c311, some c577, some c376, some c571, some c576, some c170, some c113, some c107, some c131, some c19, some c47, some c112, some c11, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c99, c309, c129, c2, c575, c300, c311, c577, c376, c571, c576, c170, c113, c107, c131, c19, c47, c112, c11] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c575 := derived575 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c577 := derived577 a h
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c571 := derived571 a h
  have h10 : Entails.eval a c576 := derived576 a h
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c112 := h 111 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c99, some c309, some c556, some c375, some c574, some c578, some c154, some c285, some c563, some c81, some c370, some c287, some c353, some c51, some c569, some c571, some c311, some c190, some c34, some c203, some c47, some c21, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c573, c99, c309, c556, c375, c574, c578, c154, c285, c563, c81, c370, c287, c353, c51, c569, c571, c311, c190, c34, c203, c47, c21] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c574 := derived574 a h
  have h6 : Entails.eval a c578 := derived578 a h
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c563 := derived563 a h
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c287 := h 286 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c569 := derived569 a h
  have h16 : Entails.eval a c571 := derived571 a h
  have h17 : Entails.eval a c311 := h 310 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c375, some c573, some c579, some c68, some c285, some c70, some c154, some c2, some c129, some c171, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c556, c375, c573, c579, c68, c285, c70, c154, c2, c129, c171] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c573 := derived573 a h
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived580

end CochromaticTwenty.Certificates.B16_8_2
