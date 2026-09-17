import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps0800_0899

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1319 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨1, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1319 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c681, some c85, some c94, some c672, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1319 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1319 : lratChecker f1319 p1319 = .success := by decide +kernel
theorem unsat1319 : Unsatisfiable (PosFin 57) f1319 := by
  apply lratCheckerSound f1319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1319
  · intro a ha; simp [p1319] at ha; subst a; trivial
  · exact checked1319
theorem derived1319 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1319 := by
  apply localUnsat_implies_entails f1319 [c681, c85, c94, c672] c1319 unsat1319 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1320 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1320 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c103, some c1282, some c66, some c1073, some c1319, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1320 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1320 : lratChecker f1320 p1320 = .success := by decide +kernel
theorem unsat1320 : Unsatisfiable (PosFin 57) f1320 := by
  apply lratCheckerSound f1320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1320
  · intro a ha; simp [p1320] at ha; subst a; trivial
  · exact checked1320
theorem derived1320 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1320 := by
  apply localUnsat_implies_entails f1320 [c97, c103, c1282, c66, c1073, c1319] c1320 unsat1320 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1073 := derived1073 a h
  have h5 : Entails.eval a c1319 := derived1319 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1321 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1321 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c1320, some c1282, some c75, some c76, some c371, some c1073, some c882, some c72, some c375, some c66, some c377, some c378, some c149, some c360, some c1066, some c516, some c1050, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1321 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1321 : lratChecker f1321 p1321 = .success := by decide +kernel
theorem unsat1321 : Unsatisfiable (PosFin 57) f1321 := by
  apply lratCheckerSound f1321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1321
  · intro a ha; simp [p1321] at ha; subst a; trivial
  · exact checked1321
theorem derived1321 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1321 := by
  apply localUnsat_implies_entails f1321 [c101, c104, c1320, c1282, c75, c76, c371, c1073, c882, c72, c375, c66, c377, c378, c149, c360, c1066, c516, c1050] c1321 unsat1321 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1320 := derived1320 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c1073 := derived1073 a h
  have h8 : Entails.eval a c882 := derived882 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c1066 := derived1066 a h
  have h17 : Entails.eval a c516 := derived516 a h
  have h18 : Entails.eval a c1050 := derived1050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1322 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1322 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c1320, some c1282, some c76, some c75, some c371, some c1073, some c882, some c72, some c375, some c1321, some c147, some c419, some c3, some c2, some c1069, some c159, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1322 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1322 : lratChecker f1322 p1322 = .success := by decide +kernel
theorem unsat1322 : Unsatisfiable (PosFin 57) f1322 := by
  apply lratCheckerSound f1322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1322
  · intro a ha; simp [p1322] at ha; subst a; trivial
  · exact checked1322
theorem derived1322 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1322 := by
  apply localUnsat_implies_entails f1322 [c101, c104, c1320, c1282, c76, c75, c371, c1073, c882, c72, c375, c1321, c147, c419, c3, c2, c1069, c159] c1322 unsat1322 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1320 := derived1320 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c1073 := derived1073 a h
  have h8 : Entails.eval a c882 := derived882 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c1321 := derived1321 a h
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c419 := derived419 a h
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c1069 := derived1069 a h
  have h17 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1323 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c378, some c818, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1323 : lratChecker f1323 p1323 = .success := by decide +kernel
theorem unsat1323 : Unsatisfiable (PosFin 57) f1323 := by
  apply lratCheckerSound f1323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1323
  · intro a ha; simp [p1323] at ha; subst a; trivial
  · exact checked1323
theorem derived1323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1323 := by
  apply localUnsat_implies_entails f1323 [c380, c378, c818] c1323 unsat1323 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1324 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1237, some c377, some c818, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1324 : lratChecker f1324 p1324 = .success := by decide +kernel
theorem unsat1324 : Unsatisfiable (PosFin 57) f1324 := by
  apply lratCheckerSound f1324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1324
  · intro a ha; simp [p1324] at ha; subst a; trivial
  · exact checked1324
theorem derived1324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1324 := by
  apply localUnsat_implies_entails f1324 [c1237, c377, c818] c1324 unsat1324 (by rfl) a
  have h0 : Entails.eval a c1237 := derived1237 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c818 := derived818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1325 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c516, some c364, some c374, some c75, some c360, some c375, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1325 : lratChecker f1325 p1325 = .success := by decide +kernel
theorem unsat1325 : Unsatisfiable (PosFin 57) f1325 := by
  apply lratCheckerSound f1325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1325
  · intro a ha; simp [p1325] at ha; subst a; trivial
  · exact checked1325
theorem derived1325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1325 := by
  apply localUnsat_implies_entails f1325 [c516, c364, c374, c75, c360, c375] c1325 unsat1325 (by rfl) a
  have h0 : Entails.eval a c516 := derived516 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1326 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨1, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c882, some c1322, some c101, some c104, some c1320, some c1323, some c1324, some c1325, some c1050, some c1066, some c170, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1326 : lratChecker f1326 p1326 = .success := by decide +kernel
theorem unsat1326 : Unsatisfiable (PosFin 57) f1326 := by
  apply lratCheckerSound f1326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1326
  · intro a ha; simp [p1326] at ha; subst a; trivial
  · exact checked1326
theorem derived1326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1326 := by
  apply localUnsat_implies_entails f1326 [c882, c1322, c101, c104, c1320, c1323, c1324, c1325, c1050, c1066, c170] c1326 unsat1326 (by rfl) a
  have h0 : Entails.eval a c882 := derived882 a h
  have h1 : Entails.eval a c1322 := derived1322 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c1323 := derived1323 a h
  have h6 : Entails.eval a c1324 := derived1324 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c1050 := derived1050 a h
  have h9 : Entails.eval a c1066 := derived1066 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1327 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1322, some c101, some c104, some c1320, some c882, some c1326, some c147, some c996, some c357, some c3, some c1307, some c66, some c76, some c75, some c375, some c419, some c159, some c1226, some c516, some c1052, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1327 : lratChecker f1327 p1327 = .success := by decide +kernel
theorem unsat1327 : Unsatisfiable (PosFin 57) f1327 := by
  apply lratCheckerSound f1327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1327
  · intro a ha; simp [p1327] at ha; subst a; trivial
  · exact checked1327
theorem derived1327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1327 := by
  apply localUnsat_implies_entails f1327 [c1322, c101, c104, c1320, c882, c1326, c147, c996, c357, c3, c1307, c66, c76, c75, c375, c419, c159, c1226, c516, c1052] c1327 unsat1327 (by rfl) a
  have h0 : Entails.eval a c1322 := derived1322 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1320 := derived1320 a h
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c1326 := derived1326 a h
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c996 := derived996 a h
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1307 := derived1307 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c419 := derived419 a h
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c1226 := derived1226 a h
  have h18 : Entails.eval a c516 := derived516 a h
  have h19 : Entails.eval a c1052 := derived1052 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1328 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c672, some c381, some c86, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1328 : lratChecker f1328 p1328 = .success := by decide +kernel
theorem unsat1328 : Unsatisfiable (PosFin 57) f1328 := by
  apply lratCheckerSound f1328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1328
  · intro a ha; simp [p1328] at ha; subst a; trivial
  · exact checked1328
theorem derived1328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1328 := by
  apply localUnsat_implies_entails f1328 [c672, c381, c86] c1328 unsat1328 (by rfl) a
  have h0 : Entails.eval a c672 := derived672 a h
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1329 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨48, by decide⟩, true), (⟨55, by decide⟩, true), (⟨41, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1320, some c1043, some c154, some c1325, some c172, some c170, some c15, some c180, some c155, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1329 : lratChecker f1329 p1329 = .success := by decide +kernel
theorem unsat1329 : Unsatisfiable (PosFin 57) f1329 := by
  apply lratCheckerSound f1329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1329
  · intro a ha; simp [p1329] at ha; subst a; trivial
  · exact checked1329
theorem derived1329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1329 := by
  apply localUnsat_implies_entails f1329 [c1320, c1043, c154, c1325, c172, c170, c15, c180, c155] c1329 unsat1329 (by rfl) a
  have h0 : Entails.eval a c1320 := derived1320 a h
  have h1 : Entails.eval a c1043 := derived1043 a h
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c1325 := derived1325 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1330 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1327, some c65, some c104, some c101, some c1320, some c1328, some c87, some c378, some c1073, some c1322, some c1216, some c1329, some c384, some c905, some c1072, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1330 : lratChecker f1330 p1330 = .success := by decide +kernel
theorem unsat1330 : Unsatisfiable (PosFin 57) f1330 := by
  apply lratCheckerSound f1330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1330
  · intro a ha; simp [p1330] at ha; subst a; trivial
  · exact checked1330
theorem derived1330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1330 := by
  apply localUnsat_implies_entails f1330 [c1327, c65, c104, c101, c1320, c1328, c87, c378, c1073, c1322, c1216, c1329, c384, c905, c1072] c1330 unsat1330 (by rfl) a
  have h0 : Entails.eval a c1327 := derived1327 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c1328 := derived1328 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c1073 := derived1073 a h
  have h9 : Entails.eval a c1322 := derived1322 a h
  have h10 : Entails.eval a c1216 := derived1216 a h
  have h11 : Entails.eval a c1329 := derived1329 a h
  have h12 : Entails.eval a c384 := h 383 (by decide)
  have h13 : Entails.eval a c905 := derived905 a h
  have h14 : Entails.eval a c1072 := derived1072 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1331 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c1320, some c1327, some c65, some c1328, some c87, some c1330, some c377, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1331 : lratChecker f1331 p1331 = .success := by decide +kernel
theorem unsat1331 : Unsatisfiable (PosFin 57) f1331 := by
  apply lratCheckerSound f1331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1331
  · intro a ha; simp [p1331] at ha; subst a; trivial
  · exact checked1331
theorem derived1331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1331 := by
  apply localUnsat_implies_entails f1331 [c101, c104, c1320, c1327, c65, c1328, c87, c1330, c377] c1331 unsat1331 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1320 := derived1320 a h
  have h3 : Entails.eval a c1327 := derived1327 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1328 := derived1328 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c1330 := derived1330 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1332 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c444, some c360, some c75, some c369, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1332 : lratChecker f1332 p1332 = .success := by decide +kernel
theorem unsat1332 : Unsatisfiable (PosFin 57) f1332 := by
  apply lratCheckerSound f1332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1332
  · intro a ha; simp [p1332] at ha; subst a; trivial
  · exact checked1332
theorem derived1332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1332 := by
  apply localUnsat_implies_entails f1332 [c444, c360, c75, c369] c1332 unsat1332 (by rfl) a
  have h0 : Entails.eval a c444 := derived444 a h
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1333 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c1320, some c1331, some c1067, some c1332, some c944, some c66, some c813, some c386, some c367, some c762, some c149, some c1043, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1333 : lratChecker f1333 p1333 = .success := by decide +kernel
theorem unsat1333 : Unsatisfiable (PosFin 57) f1333 := by
  apply lratCheckerSound f1333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1333
  · intro a ha; simp [p1333] at ha; subst a; trivial
  · exact checked1333
theorem derived1333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1333 := by
  apply localUnsat_implies_entails f1333 [c101, c104, c1320, c1331, c1067, c1332, c944, c66, c813, c386, c367, c762, c149, c1043] c1333 unsat1333 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1320 := derived1320 a h
  have h3 : Entails.eval a c1331 := derived1331 a h
  have h4 : Entails.eval a c1067 := derived1067 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c944 := derived944 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c386 := h 385 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c762 := derived762 a h
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1334 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c75, some c371, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1334 : lratChecker f1334 p1334 = .success := by decide +kernel
theorem unsat1334 : Unsatisfiable (PosFin 57) f1334 := by
  apply lratCheckerSound f1334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1334
  · intro a ha; simp [p1334] at ha; subst a; trivial
  · exact checked1334
theorem derived1334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1334 := by
  apply localUnsat_implies_entails f1334 [c76, c75, c371] c1334 unsat1334 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1335 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1331, some c101, some c104, some c1320, some c1334, some c367, some c1067, some c1322, some c1332, some c1333, some c383, some c378, some c675, some c762, some c905, some c149, some c1043, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1335 : lratChecker f1335 p1335 = .success := by decide +kernel
theorem unsat1335 : Unsatisfiable (PosFin 57) f1335 := by
  apply lratCheckerSound f1335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1335
  · intro a ha; simp [p1335] at ha; subst a; trivial
  · exact checked1335
theorem derived1335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1335 := by
  apply localUnsat_implies_entails f1335 [c1331, c101, c104, c1320, c1334, c367, c1067, c1322, c1332, c1333, c383, c378, c675, c762, c905, c149, c1043] c1335 unsat1335 (by rfl) a
  have h0 : Entails.eval a c1331 := derived1331 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c1320 := derived1320 a h
  have h4 : Entails.eval a c1334 := derived1334 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c1067 := derived1067 a h
  have h7 : Entails.eval a c1322 := derived1322 a h
  have h8 : Entails.eval a c1332 := derived1332 a h
  have h9 : Entails.eval a c1333 := derived1333 a h
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c675 := derived675 a h
  have h13 : Entails.eval a c762 := derived762 a h
  have h14 : Entails.eval a c905 := derived905 a h
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1336 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1335, some c1322, some c101, some c104, some c1320, some c1324, some c1328, some c377, some c87, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1336 : lratChecker f1336 p1336 = .success := by decide +kernel
theorem unsat1336 : Unsatisfiable (PosFin 57) f1336 := by
  apply lratCheckerSound f1336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1336
  · intro a ha; simp [p1336] at ha; subst a; trivial
  · exact checked1336
theorem derived1336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1336 := by
  apply localUnsat_implies_entails f1336 [c1335, c1322, c101, c104, c1320, c1324, c1328, c377, c87] c1336 unsat1336 (by rfl) a
  have h0 : Entails.eval a c1335 := derived1335 a h
  have h1 : Entails.eval a c1322 := derived1322 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c1324 := derived1324 a h
  have h6 : Entails.eval a c1328 := derived1328 a h
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1337 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c247, some c114, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1337 : lratChecker f1337 p1337 = .success := by decide +kernel
theorem unsat1337 : Unsatisfiable (PosFin 57) f1337 := by
  apply lratCheckerSound f1337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1337
  · intro a ha; simp [p1337] at ha; subst a; trivial
  · exact checked1337
theorem derived1337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1337 := by
  apply localUnsat_implies_entails f1337 [c249, c247, c114] c1337 unsat1337 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1338 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c101, some c1331, some c1067, some c150, some c12, some c1336, some c1320, some c1334, some c367, some c1322, some c944, some c86, some c813, some c364, some c374, some c151, some c160, some c11, some c167, some c179, some c177, some c180, some c1337, some c108, some c115, some c225, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1338 : lratChecker f1338 p1338 = .success := by decide +kernel
theorem unsat1338 : Unsatisfiable (PosFin 57) f1338 := by
  apply lratCheckerSound f1338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1338
  · intro a ha; simp [p1338] at ha; subst a; trivial
  · exact checked1338
theorem derived1338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1338 := by
  apply localUnsat_implies_entails f1338 [c104, c101, c1331, c1067, c150, c12, c1336, c1320, c1334, c367, c1322, c944, c86, c813, c364, c374, c151, c160, c11, c167, c179, c177, c180, c1337, c108, c115, c225] c1338 unsat1338 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c1331 := derived1331 a h
  have h3 : Entails.eval a c1067 := derived1067 a h
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c1320 := derived1320 a h
  have h8 : Entails.eval a c1334 := derived1334 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c1322 := derived1322 a h
  have h11 : Entails.eval a c944 := derived944 a h
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c813 := derived813 a h
  have h14 : Entails.eval a c364 := h 363 (by decide)
  have h15 : Entails.eval a c374 := h 373 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c179 := h 178 (by decide)
  have h21 : Entails.eval a c177 := h 176 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  have h23 : Entails.eval a c1337 := derived1337 a h
  have h24 : Entails.eval a c108 := h 107 (by decide)
  have h25 : Entails.eval a c115 := h 114 (by decide)
  have h26 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1339 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c115, some c225, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1339 : lratChecker f1339 p1339 = .success := by decide +kernel
theorem unsat1339 : Unsatisfiable (PosFin 57) f1339 := by
  apply lratCheckerSound f1339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1339
  · intro a ha; simp [p1339] at ha; subst a; trivial
  · exact checked1339
theorem derived1339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1339 := by
  apply localUnsat_implies_entails f1339 [c108, c115, c225] c1339 unsat1339 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1340 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1336, some c1335, some c1331, some c101, some c104, some c1320, some c1334, some c367, some c1067, some c1322, some c150, some c12, some c1338, some c382, some c364, some c1307, some c374, some c1216, some c151, some c160, some c1217, some c11, some c1209, some c167, some c179, some c177, some c180, some c1339, some c247, some c114, some c220, some c233, some c196, some c194, some c268, some c320, some c36, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1340 : lratChecker f1340 p1340 = .success := by decide +kernel
theorem unsat1340 : Unsatisfiable (PosFin 57) f1340 := by
  apply lratCheckerSound f1340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1340
  · intro a ha; simp [p1340] at ha; subst a; trivial
  · exact checked1340
theorem derived1340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1340 := by
  apply localUnsat_implies_entails f1340 [c1336, c1335, c1331, c101, c104, c1320, c1334, c367, c1067, c1322, c150, c12, c1338, c382, c364, c1307, c374, c1216, c151, c160, c1217, c11, c1209, c167, c179, c177, c180, c1339, c247, c114, c220, c233, c196, c194, c268, c320, c36] c1340 unsat1340 (by rfl) a
  have h0 : Entails.eval a c1336 := derived1336 a h
  have h1 : Entails.eval a c1335 := derived1335 a h
  have h2 : Entails.eval a c1331 := derived1331 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1320 := derived1320 a h
  have h6 : Entails.eval a c1334 := derived1334 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c1067 := derived1067 a h
  have h9 : Entails.eval a c1322 := derived1322 a h
  have h10 : Entails.eval a c150 := h 149 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1338 := derived1338 a h
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c364 := h 363 (by decide)
  have h15 : Entails.eval a c1307 := derived1307 a h
  have h16 : Entails.eval a c374 := h 373 (by decide)
  have h17 : Entails.eval a c1216 := derived1216 a h
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c1217 := derived1217 a h
  have h21 : Entails.eval a c11 := h 10 (by decide)
  have h22 : Entails.eval a c1209 := derived1209 a h
  have h23 : Entails.eval a c167 := h 166 (by decide)
  have h24 : Entails.eval a c179 := h 178 (by decide)
  have h25 : Entails.eval a c177 := h 176 (by decide)
  have h26 : Entails.eval a c180 := h 179 (by decide)
  have h27 : Entails.eval a c1339 := derived1339 a h
  have h28 : Entails.eval a c247 := h 246 (by decide)
  have h29 : Entails.eval a c114 := h 113 (by decide)
  have h30 : Entails.eval a c220 := h 219 (by decide)
  have h31 : Entails.eval a c233 := h 232 (by decide)
  have h32 : Entails.eval a c196 := h 195 (by decide)
  have h33 : Entails.eval a c194 := h 193 (by decide)
  have h34 : Entails.eval a c268 := h 267 (by decide)
  have h35 : Entails.eval a c320 := h 319 (by decide)
  have h36 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1341 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c246, some c249, some c112, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1341 : lratChecker f1341 p1341 = .success := by decide +kernel
theorem unsat1341 : Unsatisfiable (PosFin 57) f1341 := by
  apply lratCheckerSound f1341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1341
  · intro a ha; simp [p1341] at ha; subst a; trivial
  · exact checked1341
theorem derived1341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1341 := by
  apply localUnsat_implies_entails f1341 [c246, c249, c112] c1341 unsat1341 (by rfl) a
  have h0 : Entails.eval a c246 := h 245 (by decide)
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1342 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨9, by decide⟩, false), (⟨48, by decide⟩, false), (⟨12, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c107, some c251, some c225, some c196, some c205, some c119, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1342 : lratChecker f1342 p1342 = .success := by decide +kernel
theorem unsat1342 : Unsatisfiable (PosFin 57) f1342 := by
  apply lratCheckerSound f1342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1342
  · intro a ha; simp [p1342] at ha; subst a; trivial
  · exact checked1342
theorem derived1342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1342 := by
  apply localUnsat_implies_entails f1342 [c112, c107, c251, c225, c196, c205, c119] c1342 unsat1342 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1343 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨50, by decide⟩, true), (⟨52, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c944, some c813, some c101, some c86, some c104, some c1334, some c367, some c1067, some c12, some c15, some c1294, some c159, some c154, some c167, some c1209, some c179, some c177, some c1341, some c1339, some c1342, some c220, some c233, some c196, some c205, some c119, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1343 : lratChecker f1343 p1343 = .success := by decide +kernel
theorem unsat1343 : Unsatisfiable (PosFin 57) f1343 := by
  apply lratCheckerSound f1343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1343
  · intro a ha; simp [p1343] at ha; subst a; trivial
  · exact checked1343
theorem derived1343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1343 := by
  apply localUnsat_implies_entails f1343 [c944, c813, c101, c86, c104, c1334, c367, c1067, c12, c15, c1294, c159, c154, c167, c1209, c179, c177, c1341, c1339, c1342, c220, c233, c196, c205, c119] c1343 unsat1343 (by rfl) a
  have h0 : Entails.eval a c944 := derived944 a h
  have h1 : Entails.eval a c813 := derived813 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1334 := derived1334 a h
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c1067 := derived1067 a h
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c1294 := derived1294 a h
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  have h14 : Entails.eval a c1209 := derived1209 a h
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c177 := h 176 (by decide)
  have h17 : Entails.eval a c1341 := derived1341 a h
  have h18 : Entails.eval a c1339 := derived1339 a h
  have h19 : Entails.eval a c1342 := derived1342 a h
  have h20 : Entails.eval a c220 := h 219 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1344 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1340, some c1336, some c1331, some c101, some c104, some c1320, some c1334, some c367, some c1067, some c1322, some c944, some c813, some c386, some c1343, some c151, some c166, some c374, some c1043, some c159, some c178, some c180, some c161, some c868, some c869, some c191, some c230, some c224, some c108, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1344 : lratChecker f1344 p1344 = .success := by decide +kernel
theorem unsat1344 : Unsatisfiable (PosFin 57) f1344 := by
  apply lratCheckerSound f1344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1344
  · intro a ha; simp [p1344] at ha; subst a; trivial
  · exact checked1344
theorem derived1344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1344 := by
  apply localUnsat_implies_entails f1344 [c1340, c1336, c1331, c101, c104, c1320, c1334, c367, c1067, c1322, c944, c813, c386, c1343, c151, c166, c374, c1043, c159, c178, c180, c161, c868, c869, c191, c230, c224, c108] c1344 unsat1344 (by rfl) a
  have h0 : Entails.eval a c1340 := derived1340 a h
  have h1 : Entails.eval a c1336 := derived1336 a h
  have h2 : Entails.eval a c1331 := derived1331 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1320 := derived1320 a h
  have h6 : Entails.eval a c1334 := derived1334 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c1067 := derived1067 a h
  have h9 : Entails.eval a c1322 := derived1322 a h
  have h10 : Entails.eval a c944 := derived944 a h
  have h11 : Entails.eval a c813 := derived813 a h
  have h12 : Entails.eval a c386 := h 385 (by decide)
  have h13 : Entails.eval a c1343 := derived1343 a h
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  have h17 : Entails.eval a c1043 := derived1043 a h
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c161 := h 160 (by decide)
  have h22 : Entails.eval a c868 := derived868 a h
  have h23 : Entails.eval a c869 := derived869 a h
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c230 := h 229 (by decide)
  have h26 : Entails.eval a c224 := h 223 (by decide)
  have h27 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1345 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨46, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨48, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c112, some c233, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1345 : lratChecker f1345 p1345 = .success := by decide +kernel
theorem unsat1345 : Unsatisfiable (PosFin 57) f1345 := by
  apply lratCheckerSound f1345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1345
  · intro a ha; simp [p1345] at ha; subst a; trivial
  · exact checked1345
theorem derived1345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1345 := by
  apply localUnsat_implies_entails f1345 [c113, c112, c233] c1345 unsat1345 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1346 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1335, some c1344, some c382, some c1340, some c383, some c1336, some c1331, some c101, some c104, some c1320, some c1334, some c367, some c1067, some c1322, some c11, some c1043, some c167, some c374, some c179, some c177, some c151, some c12, some c1294, some c1209, some c1345, some c246, some c240, some c1339, some c107, some c220, some c233, some c196, some c205, some c119, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1346 : lratChecker f1346 p1346 = .success := by decide +kernel
theorem unsat1346 : Unsatisfiable (PosFin 57) f1346 := by
  apply lratCheckerSound f1346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1346
  · intro a ha; simp [p1346] at ha; subst a; trivial
  · exact checked1346
theorem derived1346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1346 := by
  apply localUnsat_implies_entails f1346 [c1335, c1344, c382, c1340, c383, c1336, c1331, c101, c104, c1320, c1334, c367, c1067, c1322, c11, c1043, c167, c374, c179, c177, c151, c12, c1294, c1209, c1345, c246, c240, c1339, c107, c220, c233, c196, c205, c119] c1346 unsat1346 (by rfl) a
  have h0 : Entails.eval a c1335 := derived1335 a h
  have h1 : Entails.eval a c1344 := derived1344 a h
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c1340 := derived1340 a h
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c1331 := derived1331 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c1320 := derived1320 a h
  have h10 : Entails.eval a c1334 := derived1334 a h
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c1067 := derived1067 a h
  have h13 : Entails.eval a c1322 := derived1322 a h
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c1043 := derived1043 a h
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c151 := h 150 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c1294 := derived1294 a h
  have h23 : Entails.eval a c1209 := derived1209 a h
  have h24 : Entails.eval a c1345 := derived1345 a h
  have h25 : Entails.eval a c246 := h 245 (by decide)
  have h26 : Entails.eval a c240 := h 239 (by decide)
  have h27 : Entails.eval a c1339 := derived1339 a h
  have h28 : Entails.eval a c107 := h 106 (by decide)
  have h29 : Entails.eval a c220 := h 219 (by decide)
  have h30 : Entails.eval a c233 := h 232 (by decide)
  have h31 : Entails.eval a c196 := h 195 (by decide)
  have h32 : Entails.eval a c205 := h 204 (by decide)
  have h33 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1347 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨44, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c101, some c159, some c12, some c151, some c166, some c178, some c180, some c161, some c868, some c869, some c191, some c230, some c224, some c108, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1347 : lratChecker f1347 p1347 = .success := by decide +kernel
theorem unsat1347 : Unsatisfiable (PosFin 57) f1347 := by
  apply lratCheckerSound f1347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1347
  · intro a ha; simp [p1347] at ha; subst a; trivial
  · exact checked1347
theorem derived1347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1347 := by
  apply localUnsat_implies_entails f1347 [c104, c101, c159, c12, c151, c166, c178, c180, c161, c868, c869, c191, c230, c224, c108] c1347 unsat1347 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c868 := derived868 a h
  have h10 : Entails.eval a c869 := derived869 a h
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1348 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c1320, some c1322, some c1331, some c1067, some c1334, some c367, some c1335, some c1336, some c1340, some c1344, some c383, some c382, some c1347, some c996, some c1043, some c1346, some c1216, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1348 : lratChecker f1348 p1348 = .success := by decide +kernel
theorem unsat1348 : Unsatisfiable (PosFin 57) f1348 := by
  apply lratCheckerSound f1348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1348
  · intro a ha; simp [p1348] at ha; subst a; trivial
  · exact checked1348
theorem derived1348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1348 := by
  apply localUnsat_implies_entails f1348 [c101, c104, c1320, c1322, c1331, c1067, c1334, c367, c1335, c1336, c1340, c1344, c383, c382, c1347, c996, c1043, c1346, c1216] c1348 unsat1348 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c1320 := derived1320 a h
  have h3 : Entails.eval a c1322 := derived1322 a h
  have h4 : Entails.eval a c1331 := derived1331 a h
  have h5 : Entails.eval a c1067 := derived1067 a h
  have h6 : Entails.eval a c1334 := derived1334 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c1335 := derived1335 a h
  have h9 : Entails.eval a c1336 := derived1336 a h
  have h10 : Entails.eval a c1340 := derived1340 a h
  have h11 : Entails.eval a c1344 := derived1344 a h
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c1347 := derived1347 a h
  have h15 : Entails.eval a c996 := derived996 a h
  have h16 : Entails.eval a c1043 := derived1043 a h
  have h17 : Entails.eval a c1346 := derived1346 a h
  have h18 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1349 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c998, some c999, some c41, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1349 : lratChecker f1349 p1349 = .success := by decide +kernel
theorem unsat1349 : Unsatisfiable (PosFin 57) f1349 := by
  apply lratCheckerSound f1349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1349
  · intro a ha; simp [p1349] at ha; subst a; trivial
  · exact checked1349
theorem derived1349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1349 := by
  apply localUnsat_implies_entails f1349 [c998, c999, c41] c1349 unsat1349 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c999 := derived999 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1350 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c87, some c86, some c813, some c381, some c1349, some c84, some c69, some c1307, some c516, some c364, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1350 : lratChecker f1350 p1350 = .success := by decide +kernel
theorem unsat1350 : Unsatisfiable (PosFin 57) f1350 := by
  apply lratCheckerSound f1350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1350
  · intro a ha; simp [p1350] at ha; subst a; trivial
  · exact checked1350
theorem derived1350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1350 := by
  apply localUnsat_implies_entails f1350 [c66, c87, c86, c813, c381, c1349, c84, c69, c1307, c516, c364] c1350 unsat1350 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c1349 := derived1349 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c1307 := derived1307 a h
  have h9 : Entails.eval a c516 := derived516 a h
  have h10 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1351 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨42, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1307, some c374, some c65, some c84, some c82, some c981, some c982, some c271, some c315, some c35, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1351 : lratChecker f1351 p1351 = .success := by decide +kernel
theorem unsat1351 : Unsatisfiable (PosFin 57) f1351 := by
  apply lratCheckerSound f1351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1351
  · intro a ha; simp [p1351] at ha; subst a; trivial
  · exact checked1351
theorem derived1351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1351 := by
  apply localUnsat_implies_entails f1351 [c1307, c374, c65, c84, c82, c981, c982, c271, c315, c35] c1351 unsat1351 (by rfl) a
  have h0 : Entails.eval a c1307 := derived1307 a h
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c981 := derived981 a h
  have h6 : Entails.eval a c982 := derived982 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1352 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c364, some c1067, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1352 : lratChecker f1352 p1352 = .success := by decide +kernel
theorem unsat1352 : Unsatisfiable (PosFin 57) f1352 := by
  apply lratCheckerSound f1352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1352
  · intro a ha; simp [p1352] at ha; subst a; trivial
  · exact checked1352
theorem derived1352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1352 := by
  apply localUnsat_implies_entails f1352 [c357, c364, c1067] c1352 unsat1352 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c1067 := derived1067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1353 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1320, some c76, some c75, some c1334, some c987, some c65, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1353 : lratChecker f1353 p1353 = .success := by decide +kernel
theorem unsat1353 : Unsatisfiable (PosFin 57) f1353 := by
  apply lratCheckerSound f1353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1353
  · intro a ha; simp [p1353] at ha; subst a; trivial
  · exact checked1353
theorem derived1353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1353 := by
  apply localUnsat_implies_entails f1353 [c1320, c76, c75, c1334, c987, c65] c1353 unsat1353 (by rfl) a
  have h0 : Entails.eval a c1320 := derived1320 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c1334 := derived1334 a h
  have h4 : Entails.eval a c987 := derived987 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1354 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1320, some c1350, some c1353, some c1351, some c1352, some c882, some c384, some c84, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1354 : lratChecker f1354 p1354 = .success := by decide +kernel
theorem unsat1354 : Unsatisfiable (PosFin 57) f1354 := by
  apply lratCheckerSound f1354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1354
  · intro a ha; simp [p1354] at ha; subst a; trivial
  · exact checked1354
theorem derived1354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1354 := by
  apply localUnsat_implies_entails f1354 [c1320, c1350, c1353, c1351, c1352, c882, c384, c84] c1354 unsat1354 (by rfl) a
  have h0 : Entails.eval a c1320 := derived1320 a h
  have h1 : Entails.eval a c1350 := derived1350 a h
  have h2 : Entails.eval a c1353 := derived1353 a h
  have h3 : Entails.eval a c1351 := derived1351 a h
  have h4 : Entails.eval a c1352 := derived1352 a h
  have h5 : Entails.eval a c882 := derived882 a h
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1355 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨45, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c82, some c1282, some c444, some c73, some c1307, some c1043, some c154, some c149, some c170, some c849, some c277, some c3, some c189, some c155, some c28, some c222, some c226, some c184, some c107, some c146, some c131, some c194, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1355 : lratChecker f1355 p1355 = .success := by decide +kernel
theorem unsat1355 : Unsatisfiable (PosFin 57) f1355 := by
  apply lratCheckerSound f1355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1355
  · intro a ha; simp [p1355] at ha; subst a; trivial
  · exact checked1355
theorem derived1355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1355 := by
  apply localUnsat_implies_entails f1355 [c1348, c82, c1282, c444, c73, c1307, c1043, c154, c149, c170, c849, c277, c3, c189, c155, c28, c222, c226, c184, c107, c146, c131, c194] c1355 unsat1355 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c444 := derived444 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c1307 := derived1307 a h
  have h6 : Entails.eval a c1043 := derived1043 a h
  have h7 : Entails.eval a c154 := h 153 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c849 := derived849 a h
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c189 := h 188 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c222 := h 221 (by decide)
  have h17 : Entails.eval a c226 := h 225 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c146 := h 145 (by decide)
  have h21 : Entails.eval a c131 := h 130 (by decide)
  have h22 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1356 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1320, some c1350, some c1354, some c377, some c1325, some c69, some c82, some c981, some c982, some c1355, some c76, some c1334, some c987, some c1073, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1356 : lratChecker f1356 p1356 = .success := by decide +kernel
theorem unsat1356 : Unsatisfiable (PosFin 57) f1356 := by
  apply lratCheckerSound f1356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1356
  · intro a ha; simp [p1356] at ha; subst a; trivial
  · exact checked1356
theorem derived1356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1356 := by
  apply localUnsat_implies_entails f1356 [c1348, c1320, c1350, c1354, c377, c1325, c69, c82, c981, c982, c1355, c76, c1334, c987, c1073] c1356 unsat1356 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1320 := derived1320 a h
  have h2 : Entails.eval a c1350 := derived1350 a h
  have h3 : Entails.eval a c1354 := derived1354 a h
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c1325 := derived1325 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c981 := derived981 a h
  have h9 : Entails.eval a c982 := derived982 a h
  have h10 : Entails.eval a c1355 := derived1355 a h
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c1334 := derived1334 a h
  have h13 : Entails.eval a c987 := derived987 a h
  have h14 : Entails.eval a c1073 := derived1073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1357 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1320, some c1348, some c1350, some c1356, some c384, some c905, some c93, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1357 : lratChecker f1357 p1357 = .success := by decide +kernel
theorem unsat1357 : Unsatisfiable (PosFin 57) f1357 := by
  apply lratCheckerSound f1357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1357
  · intro a ha; simp [p1357] at ha; subst a; trivial
  · exact checked1357
theorem derived1357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1357 := by
  apply localUnsat_implies_entails f1357 [c1320, c1348, c1350, c1356, c384, c905, c93] c1357 unsat1357 (by rfl) a
  have h0 : Entails.eval a c1320 := derived1320 a h
  have h1 : Entails.eval a c1348 := derived1348 a h
  have h2 : Entails.eval a c1350 := derived1350 a h
  have h3 : Entails.eval a c1356 := derived1356 a h
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c905 := derived905 a h
  have h6 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1358 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1357, some c1348, some c66, some c87, some c1282, some c813, some c380, some c386, some c84, some c69, some c1307, some c996, some c516, some c357, some c367, some c159, some c3, some c166, some c186, some c161, some c868, some c869, some c39, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1358 : lratChecker f1358 p1358 = .success := by decide +kernel
theorem unsat1358 : Unsatisfiable (PosFin 57) f1358 := by
  apply lratCheckerSound f1358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1358
  · intro a ha; simp [p1358] at ha; subst a; trivial
  · exact checked1358
theorem derived1358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1358 := by
  apply localUnsat_implies_entails f1358 [c1357, c1348, c66, c87, c1282, c813, c380, c386, c84, c69, c1307, c996, c516, c357, c367, c159, c3, c166, c186, c161, c868, c869, c39] c1358 unsat1358 (by rfl) a
  have h0 : Entails.eval a c1357 := derived1357 a h
  have h1 : Entails.eval a c1348 := derived1348 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c1307 := derived1307 a h
  have h11 : Entails.eval a c996 := derived996 a h
  have h12 : Entails.eval a c516 := derived516 a h
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c868 := derived868 a h
  have h21 : Entails.eval a c869 := derived869 a h
  have h22 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1359 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1320, some c1357, some c1358, some c378, some c383, some c1115, some c1353, some c1351, some c84, some c69, some c357, some c1043, some c516, some c367, some c159, some c3, some c166, some c186, some c161, some c868, some c869, some c39, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1359 : lratChecker f1359 p1359 = .success := by decide +kernel
theorem unsat1359 : Unsatisfiable (PosFin 57) f1359 := by
  apply lratCheckerSound f1359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1359
  · intro a ha; simp [p1359] at ha; subst a; trivial
  · exact checked1359
theorem derived1359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1359 := by
  apply localUnsat_implies_entails f1359 [c1348, c1320, c1357, c1358, c378, c383, c1115, c1353, c1351, c84, c69, c357, c1043, c516, c367, c159, c3, c166, c186, c161, c868, c869, c39] c1359 unsat1359 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1320 := derived1320 a h
  have h2 : Entails.eval a c1357 := derived1357 a h
  have h3 : Entails.eval a c1358 := derived1358 a h
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c1115 := derived1115 a h
  have h7 : Entails.eval a c1353 := derived1353 a h
  have h8 : Entails.eval a c1351 := derived1351 a h
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c1043 := derived1043 a h
  have h13 : Entails.eval a c516 := derived516 a h
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c868 := derived868 a h
  have h21 : Entails.eval a c869 := derived869 a h
  have h22 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1360 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c1282, some c98, some c543, some c65, some c368, some c367, some c150, some c364, some c13, some c374, some c82, some c1211, some c1209, some c153, some c998, some c999, some c267, some c320, some c328, some c56, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1360 : lratChecker f1360 p1360 = .success := by decide +kernel
theorem unsat1360 : Unsatisfiable (PosFin 57) f1360 := by
  apply lratCheckerSound f1360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1360
  · intro a ha; simp [p1360] at ha; subst a; trivial
  · exact checked1360
theorem derived1360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1360 := by
  apply localUnsat_implies_entails f1360 [c905, c1282, c98, c543, c65, c368, c367, c150, c364, c13, c374, c82, c1211, c1209, c153, c998, c999, c267, c320, c328, c56] c1360 unsat1360 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c1211 := derived1211 a h
  have h13 : Entails.eval a c1209 := derived1209 a h
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c998 := derived998 a h
  have h16 : Entails.eval a c999 := derived999 a h
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c320 := h 319 (by decide)
  have h19 : Entails.eval a c328 := h 327 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1361 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c98, some c1360, some c379, some c444, some c73, some c373, some c374, some c364, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1361 : lratChecker f1361 p1361 = .success := by decide +kernel
theorem unsat1361 : Unsatisfiable (PosFin 57) f1361 := by
  apply lratCheckerSound f1361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1361
  · intro a ha; simp [p1361] at ha; subst a; trivial
  · exact checked1361
theorem derived1361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1361 := by
  apply localUnsat_implies_entails f1361 [c905, c98, c1360, c379, c444, c73, c373, c374, c364] c1361 unsat1361 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1360 := derived1360 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c444 := derived444 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1362 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c1219, some c82, some c320, some c328, some c56, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1362 : lratChecker f1362 p1362 = .success := by decide +kernel
theorem unsat1362 : Unsatisfiable (PosFin 57) f1362 := by
  apply lratCheckerSound f1362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1362
  · intro a ha; simp [p1362] at ha; subst a; trivial
  · exact checked1362
theorem derived1362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1362 := by
  apply localUnsat_implies_entails f1362 [c374, c1219, c82, c320, c328, c56] c1362 unsat1362 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c1219 := derived1219 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1363 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨9, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, true), (⟨47, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c221, some c230, some c105, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1363 : lratChecker f1363 p1363 = .success := by decide +kernel
theorem unsat1363 : Unsatisfiable (PosFin 57) f1363 := by
  apply lratCheckerSound f1363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1363
  · intro a ha; simp [p1363] at ha; subst a; trivial
  · exact checked1363
theorem derived1363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1363 := by
  apply localUnsat_implies_entails f1363 [c221, c230, c105] c1363 unsat1363 (by rfl) a
  have h0 : Entails.eval a c221 := h 220 (by decide)
  have h1 : Entails.eval a c230 := h 229 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1364 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1359, some c66, some c1282, some c103, some c86, some c1361, some c905, some c98, some c543, some c65, some c386, some c368, some c367, some c1362, some c1043, some c154, some c366, some c159, some c823, some c1211, some c13, some c169, some c178, some c1363, some c1121, some c947, some c275, some c268, some c43, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1364 : lratChecker f1364 p1364 = .success := by decide +kernel
theorem unsat1364 : Unsatisfiable (PosFin 57) f1364 := by
  apply lratCheckerSound f1364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1364
  · intro a ha; simp [p1364] at ha; subst a; trivial
  · exact checked1364
theorem derived1364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1364 := by
  apply localUnsat_implies_entails f1364 [c1348, c1359, c66, c1282, c103, c86, c1361, c905, c98, c543, c65, c386, c368, c367, c1362, c1043, c154, c366, c159, c823, c1211, c13, c169, c178, c1363, c1121, c947, c275, c268, c43] c1364 unsat1364 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1359 := derived1359 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c1361 := derived1361 a h
  have h7 : Entails.eval a c905 := derived905 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c543 := derived543 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c386 := h 385 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c1362 := derived1362 a h
  have h15 : Entails.eval a c1043 := derived1043 a h
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c366 := h 365 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c823 := derived823 a h
  have h20 : Entails.eval a c1211 := derived1211 a h
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c169 := h 168 (by decide)
  have h23 : Entails.eval a c178 := h 177 (by decide)
  have h24 : Entails.eval a c1363 := derived1363 a h
  have h25 : Entails.eval a c1121 := derived1121 a h
  have h26 : Entails.eval a c947 := derived947 a h
  have h27 : Entails.eval a c275 := h 274 (by decide)
  have h28 : Entails.eval a c268 := h 267 (by decide)
  have h29 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1365 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c114, some c245, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1365 : lratChecker f1365 p1365 = .success := by decide +kernel
theorem unsat1365 : Unsatisfiable (PosFin 57) f1365 := by
  apply lratCheckerSound f1365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1365
  · intro a ha; simp [p1365] at ha; subst a; trivial
  · exact checked1365
theorem derived1365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1365 := by
  apply localUnsat_implies_entails f1365 [c112, c114, c245] c1365 unsat1365 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1366 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1365, some c226, some c109, some c110, some c245, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1366 : lratChecker f1366 p1366 = .success := by decide +kernel
theorem unsat1366 : Unsatisfiable (PosFin 57) f1366 := by
  apply lratCheckerSound f1366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1366
  · intro a ha; simp [p1366] at ha; subst a; trivial
  · exact checked1366
theorem derived1366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1366 := by
  apply localUnsat_implies_entails f1366 [c1365, c226, c109, c110, c245] c1366 unsat1366 (by rfl) a
  have h0 : Entails.eval a c1365 := derived1365 a h
  have h1 : Entails.eval a c226 := h 225 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1367 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c236, some c245, some c105, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1367 : lratChecker f1367 p1367 = .success := by decide +kernel
theorem unsat1367 : Unsatisfiable (PosFin 57) f1367 := by
  apply lratCheckerSound f1367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1367
  · intro a ha; simp [p1367] at ha; subst a; trivial
  · exact checked1367
theorem derived1367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1367 := by
  apply localUnsat_implies_entails f1367 [c236, c245, c105] c1367 unsat1367 (by rfl) a
  have h0 : Entails.eval a c236 := h 235 (by decide)
  have h1 : Entails.eval a c245 := h 244 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1368 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c287, some c296, some c43, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1368 : lratChecker f1368 p1368 = .success := by decide +kernel
theorem unsat1368 : Unsatisfiable (PosFin 57) f1368 := by
  apply lratCheckerSound f1368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1368
  · intro a ha; simp [p1368] at ha; subst a; trivial
  · exact checked1368
theorem derived1368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1368 := by
  apply localUnsat_implies_entails f1368 [c287, c296, c43] c1368 unsat1368 (by rfl) a
  have h0 : Entails.eval a c287 := h 286 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1369 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c63, some c332, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1369 : lratChecker f1369 p1369 = .success := by decide +kernel
theorem unsat1369 : Unsatisfiable (PosFin 57) f1369 := by
  apply lratCheckerSound f1369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1369
  · intro a ha; simp [p1369] at ha; subst a; trivial
  · exact checked1369
theorem derived1369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1369 := by
  apply localUnsat_implies_entails f1369 [c54, c63, c332] c1369 unsat1369 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1370 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1359, some c98, some c1348, some c66, some c1282, some c103, some c86, some c905, some c1361, some c1364, some c380, some c379, some c1362, some c1043, some c149, some c367, some c73, some c1369, some c947, some c275, some c43, some c52, some c288, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1370 : lratChecker f1370 p1370 = .success := by decide +kernel
theorem unsat1370 : Unsatisfiable (PosFin 57) f1370 := by
  apply lratCheckerSound f1370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1370
  · intro a ha; simp [p1370] at ha; subst a; trivial
  · exact checked1370
theorem derived1370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1370 := by
  apply localUnsat_implies_entails f1370 [c1359, c98, c1348, c66, c1282, c103, c86, c905, c1361, c1364, c380, c379, c1362, c1043, c149, c367, c73, c1369, c947, c275, c43, c52, c288] c1370 unsat1370 (by rfl) a
  have h0 : Entails.eval a c1359 := derived1359 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1348 := derived1348 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c905 := derived905 a h
  have h8 : Entails.eval a c1361 := derived1361 a h
  have h9 : Entails.eval a c1364 := derived1364 a h
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c1362 := derived1362 a h
  have h13 : Entails.eval a c1043 := derived1043 a h
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c367 := h 366 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c1369 := derived1369 a h
  have h18 : Entails.eval a c947 := derived947 a h
  have h19 : Entails.eval a c275 := h 274 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c52 := h 51 (by decide)
  have h22 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1371 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c383, some c543, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1371 : lratChecker f1371 p1371 = .success := by decide +kernel
theorem unsat1371 : Unsatisfiable (PosFin 57) f1371 := by
  apply lratCheckerSound f1371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1371
  · intro a ha; simp [p1371] at ha; subst a; trivial
  · exact checked1371
theorem derived1371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1371 := by
  apply localUnsat_implies_entails f1371 [c378, c383, c543] c1371 unsat1371 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c543 := derived543 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1372 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c374, some c364, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1372 : lratChecker f1372 p1372 = .success := by decide +kernel
theorem unsat1372 : Unsatisfiable (PosFin 57) f1372 := by
  apply lratCheckerSound f1372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1372
  · intro a ha; simp [p1372] at ha; subst a; trivial
  · exact checked1372
theorem derived1372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1372 := by
  apply localUnsat_implies_entails f1372 [c373, c374, c364] c1372 unsat1372 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1373 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1371, some c98, some c1361, some c93, some c70, some c384, some c981, some c982, some c1372, some c73, some c271, some c315, some c35, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1373 : lratChecker f1373 p1373 = .success := by decide +kernel
theorem unsat1373 : Unsatisfiable (PosFin 57) f1373 := by
  apply lratCheckerSound f1373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1373
  · intro a ha; simp [p1373] at ha; subst a; trivial
  · exact checked1373
theorem derived1373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1373 := by
  apply localUnsat_implies_entails f1373 [c1371, c98, c1361, c93, c70, c384, c981, c982, c1372, c73, c271, c315, c35] c1373 unsat1373 (by rfl) a
  have h0 : Entails.eval a c1371 := derived1371 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1361 := derived1361 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c981 := derived981 a h
  have h7 : Entails.eval a c982 := derived982 a h
  have h8 : Entails.eval a c1372 := derived1372 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1374 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c1043, some c1164, some c149, some c366, some c321, some c277, some c571, some c570, some c263, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1374 : lratChecker f1374 p1374 = .success := by decide +kernel
theorem unsat1374 : Unsatisfiable (PosFin 57) f1374 := by
  apply lratCheckerSound f1374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1374
  · intro a ha; simp [p1374] at ha; subst a; trivial
  · exact checked1374
theorem derived1374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1374 := by
  apply localUnsat_implies_entails f1374 [c364, c1043, c1164, c149, c366, c321, c277, c571, c570, c263] c1374 unsat1374 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c1043 := derived1043 a h
  have h2 : Entails.eval a c1164 := derived1164 a h
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c571 := derived571 a h
  have h8 : Entails.eval a c570 := derived570 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1375 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1374, some c375, some c284, some c328, some c360, some c1164, some c362, some c571, some c570, some c267, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1375 : lratChecker f1375 p1375 = .success := by decide +kernel
theorem unsat1375 : Unsatisfiable (PosFin 57) f1375 := by
  apply lratCheckerSound f1375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1375
  · intro a ha; simp [p1375] at ha; subst a; trivial
  · exact checked1375
theorem derived1375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1375 := by
  apply localUnsat_implies_entails f1375 [c1374, c375, c284, c328, c360, c1164, c362, c571, c570, c267] c1375 unsat1375 (by rfl) a
  have h0 : Entails.eval a c1374 := derived1374 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c1164 := derived1164 a h
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c571 := derived571 a h
  have h8 : Entails.eval a c570 := derived570 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1376 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c384, some c981, some c982, some c1375, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1376 : lratChecker f1376 p1376 = .success := by decide +kernel
theorem unsat1376 : Unsatisfiable (PosFin 57) f1376 := by
  apply lratCheckerSound f1376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1376
  · intro a ha; simp [p1376] at ha; subst a; trivial
  · exact checked1376
theorem derived1376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1376 := by
  apply localUnsat_implies_entails f1376 [c377, c384, c981, c982, c1375] c1376 unsat1376 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c981 := derived981 a h
  have h3 : Entails.eval a c982 := derived982 a h
  have h4 : Entails.eval a c1375 := derived1375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1377 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c1376, some c69, some c93, some c905, some c381, some c1076, some c1075, some c375, some c1043, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1377 : lratChecker f1377 p1377 = .success := by decide +kernel
theorem unsat1377 : Unsatisfiable (PosFin 57) f1377 := by
  apply lratCheckerSound f1377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1377
  · intro a ha; simp [p1377] at ha; subst a; trivial
  · exact checked1377
theorem derived1377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1377 := by
  apply localUnsat_implies_entails f1377 [c377, c1376, c69, c93, c905, c381, c1076, c1075, c375, c1043] c1377 unsat1377 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c1376 := derived1376 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c905 := derived905 a h
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c1076 := derived1076 a h
  have h7 : Entails.eval a c1075 := derived1075 a h
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1378 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1359, some c1370, some c1371, some c98, some c1348, some c1373, some c75, some c1377, some c543, some c65, some c981, some c982, some c271, some c315, some c35, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1378 : lratChecker f1378 p1378 = .success := by decide +kernel
theorem unsat1378 : Unsatisfiable (PosFin 57) f1378 := by
  apply lratCheckerSound f1378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1378
  · intro a ha; simp [p1378] at ha; subst a; trivial
  · exact checked1378
theorem derived1378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1378 := by
  apply localUnsat_implies_entails f1378 [c1359, c1370, c1371, c98, c1348, c1373, c75, c1377, c543, c65, c981, c982, c271, c315, c35] c1378 unsat1378 (by rfl) a
  have h0 : Entails.eval a c1359 := derived1359 a h
  have h1 : Entails.eval a c1370 := derived1370 a h
  have h2 : Entails.eval a c1371 := derived1371 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1373 := derived1373 a h
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c1377 := derived1377 a h
  have h8 : Entails.eval a c543 := derived543 a h
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c981 := derived981 a h
  have h11 : Entails.eval a c982 := derived982 a h
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1379 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c170, some c172, some c13, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1379 : lratChecker f1379 p1379 = .success := by decide +kernel
theorem unsat1379 : Unsatisfiable (PosFin 57) f1379 := by
  apply lratCheckerSound f1379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1379
  · intro a ha; simp [p1379] at ha; subst a; trivial
  · exact checked1379
theorem derived1379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1379 := by
  apply localUnsat_implies_entails f1379 [c170, c172, c13] c1379 unsat1379 (by rfl) a
  have h0 : Entails.eval a c170 := h 169 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1380 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c174, some c176, some c13, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1380 : lratChecker f1380 p1380 = .success := by decide +kernel
theorem unsat1380 : Unsatisfiable (PosFin 57) f1380 := by
  apply lratCheckerSound f1380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1380
  · intro a ha; simp [p1380] at ha; subst a; trivial
  · exact checked1380
theorem derived1380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1380 := by
  apply localUnsat_implies_entails f1380 [c174, c176, c13] c1380 unsat1380 (by rfl) a
  have h0 : Entails.eval a c174 := h 173 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1381 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c103, some c1359, some c98, some c1370, some c667, some c72, some c377, some c1282, some c1371, some c1348, some c1379, some c10, some c1380, some c182, some c157, some c375, some c360, some c362, some c1164, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c1378, c103, c1359, c98, c1370, c667, c72, c377, c1282, c1371, c1348, c1379, c10, c1380, c182, c157, c375, c360, c362, c1164] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1359 := derived1359 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1370 := derived1370 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1371 := derived1371 a h
  have h10 : Entails.eval a c1348 := derived1348 a h
  have h11 : Entails.eval a c1379 := derived1379 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c1380 := derived1380 a h
  have h14 : Entails.eval a c182 := h 181 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c375 := h 374 (by decide)
  have h17 : Entails.eval a c360 := h 359 (by decide)
  have h18 : Entails.eval a c362 := h 361 (by decide)
  have h19 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c170, some c149, some c13, some c375, some c363, some c1164, some c158, some c539, some c436, some c105, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c98, c170, c149, c13, c375, c363, c1164, c158, c539, c436, c105] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c1164 := derived1164 a h
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c539 := derived539 a h
  have h9 : Entails.eval a c436 := derived436 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1381, some c381, some c1378, some c103, some c1359, some c98, some c1370, some c667, some c72, some c377, some c1282, some c1371, some c1348, some c571, some c570, some c193, some c33, some c247, some c238, some c1382, some c10, some c152, some c173, some c114, some c375, some c539, some c360, some c1164, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c1381, c381, c1378, c103, c1359, c98, c1370, c667, c72, c377, c1282, c1371, c1348, c571, c570, c193, c33, c247, c238, c1382, c10, c152, c173, c114, c375, c539, c360, c1164] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c1381 := derived1381 a h
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c1378 := derived1378 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c1359 := derived1359 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1370 := derived1370 a h
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c1371 := derived1371 a h
  have h12 : Entails.eval a c1348 := derived1348 a h
  have h13 : Entails.eval a c571 := derived571 a h
  have h14 : Entails.eval a c570 := derived570 a h
  have h15 : Entails.eval a c193 := h 192 (by decide)
  have h16 : Entails.eval a c33 := h 32 (by decide)
  have h17 : Entails.eval a c247 := h 246 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  have h19 : Entails.eval a c1382 := derived1382 a h
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c114 := h 113 (by decide)
  have h24 : Entails.eval a c375 := h 374 (by decide)
  have h25 : Entails.eval a c539 := derived539 a h
  have h26 : Entails.eval a c360 := h 359 (by decide)
  have h27 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, true), (⟨52, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c170, some c149, some c171, some c375, some c539, some c363, some c1164, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c170, c149, c171, c375, c539, c363, c1164] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c170 := h 169 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c539 := derived539 a h
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1378, some c103, some c1282, some c1359, some c1370, some c1371, some c98, some c1348, some c377, some c667, some c72, some c1381, some c381, some c1383, some c1384, some c10, some c152, some c603, some c375, some c1164, some c360, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c1378, c103, c1282, c1359, c1370, c1371, c98, c1348, c377, c667, c72, c1381, c381, c1383, c1384, c10, c152, c603, c375, c1164, c360] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c1378 := derived1378 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1359 := derived1359 a h
  have h4 : Entails.eval a c1370 := derived1370 a h
  have h5 : Entails.eval a c1371 := derived1371 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c667 := derived667 a h
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c1381 := derived1381 a h
  have h12 : Entails.eval a c381 := h 380 (by decide)
  have h13 : Entails.eval a c1383 := derived1383 a h
  have h14 : Entails.eval a c1384 := derived1384 a h
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c603 := derived603 a h
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c1164 := derived1164 a h
  have h20 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1359, some c98, some c1370, some c1378, some c103, some c1385, some c543, some c85, some c384, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c1359, c98, c1370, c1378, c103, c1385, c543, c85, c384] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c1359 := derived1359 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1370 := derived1370 a h
  have h3 : Entails.eval a c1378 := derived1378 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c1385 := derived1385 a h
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨42, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c1164, some c148, some c358, some c82, some c162, some c1369, some c379, some c325, some c172, some c209, some c181, some c138, some c105, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c359, c1164, c148, c358, c82, c162, c1369, c379, c325, c172, c209, c181, c138, c105] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c1164 := derived1164 a h
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c1369 := derived1369 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c181 := h 180 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c371, some c74, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c375, c371, c74] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c82, some c72, some c1369, some c326, some c42, some c282, some c43, some c52, some c288, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 57) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c1077, c82, c72, c1369, c326, c42, c282, c43, c52, c288] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1369 := derived1369 a h
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1386, some c100, some c1282, some c95, some c1348, some c378, some c380, some c359, some c1081, some c148, some c1164, some c7, some c159, some c1388, some c358, some c162, some c379, some c172, some c1389, some c16, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 57) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c1386, c100, c1282, c95, c1348, c378, c380, c359, c1081, c148, c1164, c7, c159, c1388, c358, c162, c379, c172, c1389, c16] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c1386 := derived1386 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c1081 := derived1081 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1164 := derived1164 a h
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c1388 := derived1388 a h
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c162 := h 161 (by decide)
  have h16 : Entails.eval a c379 := h 378 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c1389 := derived1389 a h
  have h19 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1390, some c1386, some c100, some c1282, some c95, some c1348, some c1081, some c148, some c7, some c422, some c170, some c1164, some c379, some c359, some c358, some c173, some c813, some c72, some c174, some c375, some c1015, some c184, some c16, some c160, some c970, some c42, some c328, some c326, some c63, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 57) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c1390, c1386, c100, c1282, c95, c1348, c1081, c148, c7, c422, c170, c1164, c379, c359, c358, c173, c813, c72, c174, c375, c1015, c184, c16, c160, c970, c42, c328, c326, c63] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c1390 := derived1390 a h
  have h1 : Entails.eval a c1386 := derived1386 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c1081 := derived1081 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c422 := derived422 a h
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c1164 := derived1164 a h
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c359 := h 358 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c813 := derived813 a h
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c375 := h 374 (by decide)
  have h20 : Entails.eval a c1015 := derived1015 a h
  have h21 : Entails.eval a c184 := h 183 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c160 := h 159 (by decide)
  have h24 : Entails.eval a c970 := derived970 a h
  have h25 : Entails.eval a c42 := h 41 (by decide)
  have h26 : Entails.eval a c328 := h 327 (by decide)
  have h27 : Entails.eval a c326 := h 325 (by decide)
  have h28 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨55, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c362, some c1164, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 57) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c360, c362, c1164] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c1389, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 57) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c70, c1389] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c1389 := derived1389 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1394 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c369, some c74, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 57) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c375, c369, c74] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨42, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c149, some c445, some c1392, some c1164, some c813, some c381, some c158, some c13, some c173, some c174, some c185, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 57) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c360, c149, c445, c1392, c1164, c813, c381, c158, c13, c173, c174, c185] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c445 := derived445 a h
  have h3 : Entails.eval a c1392 := derived1392 a h
  have h4 : Entails.eval a c1164 := derived1164 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1282, some c10, some c6, some c157, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 57) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c100, c1282, c10, c6, c157] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1386, some c100, some c1282, some c95, some c1348, some c1390, some c1391, some c377, some c1395, some c1394, some c1393, some c1396, some c1379, some c170, some c381, some c13, some c7, some c363, some c158, some c1164, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 57) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1386, c100, c1282, c95, c1348, c1390, c1391, c377, c1395, c1394, c1393, c1396, c1379, c170, c381, c13, c7, c363, c158, c1164] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1386 := derived1386 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1390 := derived1390 a h
  have h6 : Entails.eval a c1391 := derived1391 a h
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c1395 := derived1395 a h
  have h9 : Entails.eval a c1394 := derived1394 a h
  have h10 : Entails.eval a c1393 := derived1393 a h
  have h11 : Entails.eval a c1396 := derived1396 a h
  have h12 : Entails.eval a c1379 := derived1379 a h
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c381 := h 380 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1386, some c100, some c1282, some c95, some c1348, some c1397, some c543, some c65, some c85, some c813, some c384, some c1184, some c359, some c1185, some c1081, some c148, some c1187, some c299, some c599, some c371, some c7, some c163, some c43, some c55, some c1077, some c159, some c162, some c131, some c123, some c269, some c313, some c1188, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 57) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c1386, c100, c1282, c95, c1348, c1397, c543, c65, c85, c813, c384, c1184, c359, c1185, c1081, c148, c1187, c299, c599, c371, c7, c163, c43, c55, c1077, c159, c162, c131, c123, c269, c313, c1188] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c1386 := derived1386 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c1348 := derived1348 a h
  have h5 : Entails.eval a c1397 := derived1397 a h
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c1184 := derived1184 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c1185 := derived1185 a h
  have h14 : Entails.eval a c1081 := derived1081 a h
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c1187 := derived1187 a h
  have h17 : Entails.eval a c299 := h 298 (by decide)
  have h18 : Entails.eval a c599 := derived599 a h
  have h19 : Entails.eval a c371 := h 370 (by decide)
  have h20 : Entails.eval a c7 := h 6 (by decide)
  have h21 : Entails.eval a c163 := h 162 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c1077 := derived1077 a h
  have h25 : Entails.eval a c159 := h 158 (by decide)
  have h26 : Entails.eval a c162 := h 161 (by decide)
  have h27 : Entails.eval a c131 := h 130 (by decide)
  have h28 : Entails.eval a c123 := h 122 (by decide)
  have h29 : Entails.eval a c269 := h 268 (by decide)
  have h30 : Entails.eval a c313 := h 312 (by decide)
  have h31 : Entails.eval a c1188 := derived1188 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨30, by decide⟩, true), (⟨14, by decide⟩, false), (⟨44, by decide⟩, true), (⟨32, by decide⟩, false), (⟨47, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c163, some c679, some c123, some c146, some c139, some c259, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c74, c163, c679, c123, c146, c139, c259] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c679 := derived679 a h
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1282, some c148, some c94, some c71, some c1184, some c1164, some c159, some c1394, some c358, some c1393, some c162, some c301, some c1399, some c1187, some c278, some c73, some c1186, some c282, some c64, some c39, some c325, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1282, c148, c94, c71, c1184, c1164, c159, c1394, c358, c1393, c162, c301, c1399, c1187, c278, c73, c1186, c282, c64, c39, c325] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1282 := derived1282 a h
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c1184 := derived1184 a h
  have h5 : Entails.eval a c1164 := derived1164 a h
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c1394 := derived1394 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c1393 := derived1393 a h
  have h10 : Entails.eval a c162 := h 161 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c1399 := derived1399 a h
  have h13 : Entails.eval a c1187 := derived1187 a h
  have h14 : Entails.eval a c278 := h 277 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c1186 := derived1186 a h
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1398, some c1386, some c100, some c1282, some c95, some c1348, some c1081, some c148, some c7, some c1400, some c813, some c380, some c381, some c1201, some c72, some c174, some c358, some c184, some c375, some c160, some c326, some c39, some c282, some c44, some c53, some c289, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1398, c1386, c100, c1282, c95, c1348, c1081, c148, c7, c1400, c813, c380, c381, c1201, c72, c174, c358, c184, c375, c160, c326, c39, c282, c44, c53, c289] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1386 := derived1386 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c1081 := derived1081 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c1400 := derived1400 a h
  have h10 : Entails.eval a c813 := derived813 a h
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c381 := h 380 (by decide)
  have h13 : Entails.eval a c1201 := derived1201 a h
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c358 := h 357 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c39 := h 38 (by decide)
  have h22 : Entails.eval a c282 := h 281 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  have h24 : Entails.eval a c53 := h 52 (by decide)
  have h25 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1401, some c377, some c378, some c1398, some c1386, some c100, some c1282, some c95, some c1348, some c94, some c1392, some c1078, some c1394, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1401, c377, c378, c1398, c1386, c100, c1282, c95, c1348, c94, c1392, c1078, c1394] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1401 := derived1401 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c1398 := derived1398 a h
  have h4 : Entails.eval a c1386 := derived1386 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c1348 := derived1348 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c1392 := derived1392 a h
  have h11 : Entails.eval a c1078 := derived1078 a h
  have h12 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c571, some c570, some c41, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c571, c570, c41] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c571 := derived571 a h
  have h1 : Entails.eval a c570 := derived570 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1398, some c1386, some c100, some c1282, some c95, some c1348, some c1401, some c378, some c377, some c1402, some c813, some c381, some c72, some c1403, some c93, some c1384, some c10, some c1396, some c603, some c375, some c1164, some c360, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c1398, c1386, c100, c1282, c95, c1348, c1401, c378, c377, c1402, c813, c381, c72, c1403, c93, c1384, c10, c1396, c603, c375, c1164, c360] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1386 := derived1386 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c1348 := derived1348 a h
  have h6 : Entails.eval a c1401 := derived1401 a h
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c1402 := derived1402 a h
  have h10 : Entails.eval a c813 := derived813 a h
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c1403 := derived1403 a h
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c1384 := derived1384 a h
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c1396 := derived1396 a h
  have h18 : Entails.eval a c603 := derived603 a h
  have h19 : Entails.eval a c375 := h 374 (by decide)
  have h20 : Entails.eval a c1164 := derived1164 a h
  have h21 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1348, some c1386, some c95, some c100, some c1398, some c1404, some c65, some c85, some c813, some c1184, some c71, some c599, some c679, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1348, c1386, c95, c100, c1398, c1404, c65, c85, c813, c1184, c71, c599, c679] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1348 := derived1348 a h
  have h1 : Entails.eval a c1386 := derived1386 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c1398 := derived1398 a h
  have h5 : Entails.eval a c1404 := derived1404 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1184 := derived1184 a h
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c599 := derived599 a h
  have h12 : Entails.eval a c679 := derived679 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c66, some c1282, some c103, some c86, some c904, some c905, some c381, some c379, some c332, some c903, some c35, some c73, some c965, some c1372, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c1405, c1049, c66, c1282, c103, c86, c904, c905, c381, c379, c332, c903, c35, c73, c965, c1372] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c904 := derived904 a h
  have h7 : Entails.eval a c905 := derived905 a h
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c903 := derived903 a h
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c965 := derived965 a h
  have h15 : Entails.eval a c1372 := derived1372 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c444, some c373, some c73, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c444, c373, c73] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c444 := derived444 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1406, some c378, some c377, some c68, some c1407, some c75, some c1377, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1405, c1049, c1406, c378, c377, c68, c1407, c75, c1377] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c1407 := derived1407 a h
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c1377 := derived1377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1406, some c378, some c1408, some c103, some c92, some c667, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c1405, c1049, c1406, c378, c1408, c103, c92, c667] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c1408 := derived1408 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c667 := derived667 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c1230, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c159, c1230] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c1230 := derived1230 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c328, some c56, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c320, c328, c56] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1409, some c84, some c65, some c66, some c1282, some c368, some c367, some c103, some c68, some c80, some c86, some c386, some c371, some c905, some c366, some c374, some c1209, some c1410, some c11, some c167, some c179, some c177, some c1411, some c194, some c233, some c225, some c107, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1405, c1049, c1409, c84, c65, c66, c1282, c368, c367, c103, c68, c80, c86, c386, c371, c905, c366, c374, c1209, c1410, c11, c167, c179, c177, c1411, c194, c233, c225, c107] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1409 := derived1409 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c386 := h 385 (by decide)
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c905 := derived905 a h
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c1209 := derived1209 a h
  have h19 : Entails.eval a c1410 := derived1410 a h
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c179 := h 178 (by decide)
  have h23 : Entails.eval a c177 := h 176 (by decide)
  have h24 : Entails.eval a c1411 := derived1411 a h
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c233 := h 232 (by decide)
  have h27 : Entails.eval a c225 := h 224 (by decide)
  have h28 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1409, some c65, some c84, some c1412, some c383, some c384, some c68, some c85, some c368, some c103, some c75, some c541, some c1025, some c35, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c1405, c1049, c1409, c65, c84, c1412, c383, c384, c68, c85, c368, c103, c75, c541, c1025, c35] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1409 := derived1409 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c1412 := derived1412 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c541 := derived541 a h
  have h14 : Entails.eval a c1025 := derived1025 a h
  have h15 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c1282, some c103, some c86, some c1405, some c1049, some c904, some c332, some c35, some c965, some c288, some c68, some c1007, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 57) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c66, c1282, c103, c86, c1405, c1049, c904, c332, c35, c965, c288, c68, c1007] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c1405 := derived1405 a h
  have h5 : Entails.eval a c1049 := derived1049 a h
  have h6 : Entails.eval a c904 := derived904 a h
  have h7 : Entails.eval a c332 := h 331 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c965 := derived965 a h
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c1007 := derived1007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c1414, some c65, some c66, some c1282, some c103, some c368, some c80, some c371, some c367, some c86, some c905, some c1413, some c87, some c991, some c366, some c374, some c1209, some c1411, some c1410, some c194, some c11, some c233, some c32, some c167, some c114, some c179, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 57) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c1405, c1049, c1414, c65, c66, c1282, c103, c368, c80, c371, c367, c86, c905, c1413, c87, c991, c366, c374, c1209, c1411, c1410, c194, c11, c233, c32, c167, c114, c179] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c1414 := derived1414 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c905 := derived905 a h
  have h13 : Entails.eval a c1413 := derived1413 a h
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c991 := derived991 a h
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c1209 := derived1209 a h
  have h19 : Entails.eval a c1411 := derived1411 a h
  have h20 : Entails.eval a c1410 := derived1410 a h
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c11 := h 10 (by decide)
  have h23 : Entails.eval a c233 := h 232 (by decide)
  have h24 : Entails.eval a c32 := h 31 (by decide)
  have h25 : Entails.eval a c167 := h 166 (by decide)
  have h26 : Entails.eval a c114 := h 113 (by decide)
  have h27 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1405, some c1049, some c66, some c1282, some c103, some c86, some c905, some c1414, some c65, some c368, some c367, some c68, some c80, some c371, some c1415, some c386, some c529, some c524, some c967, some c1410, some c1043, some c1209, some c1411, some c267, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 57) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1405, c1049, c66, c1282, c103, c86, c905, c1414, c65, c368, c367, c68, c80, c371, c1415, c386, c529, c524, c967, c1410, c1043, c1209, c1411, c267] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1405 := derived1405 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c905 := derived905 a h
  have h7 : Entails.eval a c1414 := derived1414 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c371 := h 370 (by decide)
  have h14 : Entails.eval a c1415 := derived1415 a h
  have h15 : Entails.eval a c386 := h 385 (by decide)
  have h16 : Entails.eval a c529 := derived529 a h
  have h17 : Entails.eval a c524 := derived524 a h
  have h18 : Entails.eval a c967 := derived967 a h
  have h19 : Entails.eval a c1410 := derived1410 a h
  have h20 : Entails.eval a c1043 := derived1043 a h
  have h21 : Entails.eval a c1209 := derived1209 a h
  have h22 : Entails.eval a c1411 := derived1411 a h
  have h23 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1416, some c378, some c1405, some c1049, some c91, some c904, some c332, some c35, some c285, some c288, some c45, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 57) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c1416, c378, c1405, c1049, c91, c904, c332, c35, c285, c288, c45] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c1416 := derived1416 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c1405 := derived1405 a h
  have h3 : Entails.eval a c1049 := derived1049 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c904 := derived904 a h
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1416, some c1405, some c1049, some c378, some c1417, some c103, some c92, some c667, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 57) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c1416, c1405, c1049, c378, c1417, c103, c92, c667] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c1416 := derived1416 a h
  have h1 : Entails.eval a c1405 := derived1405 a h
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c1417 := derived1417 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c667 := derived667 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1418

end CochromaticTwenty.Certificates.B16_8_0Enumerating
