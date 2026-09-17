import MerLeanExperiment.Certificates.B16_8_2.Steps0900_0999

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1381 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c149, some c841, some c10, some c175, some c111, some c21, some c247, some c1372, some c109, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1381 : lratChecker f1381 p1381 = .success := by decide +kernel
theorem unsat1381 : Unsatisfiable (PosFin 57) f1381 := by
  apply lratCheckerSound f1381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1381
  · intro a ha; simp [p1381] at ha; subst a; trivial
  · exact checked1381
theorem derived1381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1381 := by
  apply localUnsat_implies_entails f1381 [c367, c149, c841, c10, c175, c111, c21, c247, c1372, c109] c1381 unsat1381 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c1372 := derived1372 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1382 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨48, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c367, some c158, some c149, some c21, some c1372, some c231, some c109, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1382 : lratChecker f1382 p1382 = .success := by decide +kernel
theorem unsat1382 : Unsatisfiable (PosFin 57) f1382 := by
  apply lratCheckerSound f1382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1382
  · intro a ha; simp [p1382] at ha; subst a; trivial
  · exact checked1382
theorem derived1382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1382 := by
  apply localUnsat_implies_entails f1382 [c10, c367, c158, c149, c21, c1372, c231, c109] c1382 unsat1382 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1372 := derived1372 a h
  have h6 : Entails.eval a c231 := h 230 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1383 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c97, some c1298, some c1344, some c80, some c68, some c1368, some c10, some c1, some c1362, some c1370, some c1377, some c1379, some c841, some c363, some c367, some c149, some c159, some c1380, some c157, some c370, some c70, some c1357, some c1088, some c1381, some c1382, some c106, some c238, some c110, some c1371, some c1069, some c36, some c144, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1383 : lratChecker f1383 p1383 = .success := by decide +kernel
theorem unsat1383 : Unsatisfiable (PosFin 57) f1383 := by
  apply lratCheckerSound f1383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1383
  · intro a ha; simp [p1383] at ha; subst a; trivial
  · exact checked1383
theorem derived1383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1383 := by
  apply localUnsat_implies_entails f1383 [c100, c97, c1298, c1344, c80, c68, c1368, c10, c1, c1362, c1370, c1377, c1379, c841, c363, c367, c149, c159, c1380, c157, c370, c70, c1357, c1088, c1381, c1382, c106, c238, c110, c1371, c1069, c36, c144] c1383 unsat1383 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1344 := derived1344 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c1368 := derived1368 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c1362 := derived1362 a h
  have h10 : Entails.eval a c1370 := derived1370 a h
  have h11 : Entails.eval a c1377 := derived1377 a h
  have h12 : Entails.eval a c1379 := derived1379 a h
  have h13 : Entails.eval a c841 := derived841 a h
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c367 := h 366 (by decide)
  have h16 : Entails.eval a c149 := h 148 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  have h18 : Entails.eval a c1380 := derived1380 a h
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c70 := h 69 (by decide)
  have h22 : Entails.eval a c1357 := derived1357 a h
  have h23 : Entails.eval a c1088 := derived1088 a h
  have h24 : Entails.eval a c1381 := derived1381 a h
  have h25 : Entails.eval a c1382 := derived1382 a h
  have h26 : Entails.eval a c106 := h 105 (by decide)
  have h27 : Entails.eval a c238 := h 237 (by decide)
  have h28 : Entails.eval a c110 := h 109 (by decide)
  have h29 : Entails.eval a c1371 := derived1371 a h
  have h30 : Entails.eval a c1069 := derived1069 a h
  have h31 : Entails.eval a c36 := h 35 (by decide)
  have h32 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1384 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨54, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1325, some c1120, some c175, some c36, some c251, some c1352, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1384 : lratChecker f1384 p1384 = .success := by decide +kernel
theorem unsat1384 : Unsatisfiable (PosFin 57) f1384 := by
  apply lratCheckerSound f1384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1384
  · intro a ha; simp [p1384] at ha; subst a; trivial
  · exact checked1384
theorem derived1384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1384 := by
  apply localUnsat_implies_entails f1384 [c1325, c1120, c175, c36, c251, c1352] c1384 unsat1384 (by rfl) a
  have h0 : Entails.eval a c1325 := derived1325 a h
  have h1 : Entails.eval a c1120 := derived1120 a h
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c251 := h 250 (by decide)
  have h5 : Entails.eval a c1352 := derived1352 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1385 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c218, some c212, some c139, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1385 : lratChecker f1385 p1385 = .success := by decide +kernel
theorem unsat1385 : Unsatisfiable (PosFin 57) f1385 := by
  apply lratCheckerSound f1385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1385
  · intro a ha; simp [p1385] at ha; subst a; trivial
  · exact checked1385
theorem derived1385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1385 := by
  apply localUnsat_implies_entails f1385 [c218, c212, c139] c1385 unsat1385 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1386 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨54, by decide⟩, false), (⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c1384, some c69, some c179, some c372, some c251, some c114, some c1385, some c163, some c326, some c236, some c60, some c672, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1386 : lratChecker f1386 p1386 = .success := by decide +kernel
theorem unsat1386 : Unsatisfiable (PosFin 57) f1386 := by
  apply lratCheckerSound f1386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1386
  · intro a ha; simp [p1386] at ha; subst a; trivial
  · exact checked1386
theorem derived1386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1386 := by
  apply localUnsat_implies_entails f1386 [c115, c1384, c69, c179, c372, c251, c114, c1385, c163, c326, c236, c60, c672] c1386 unsat1386 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c1384 := derived1384 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c1385 := derived1385 a h
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1387 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c36, some c301, some c300, some c50, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1387 : lratChecker f1387 p1387 = .success := by decide +kernel
theorem unsat1387 : Unsatisfiable (PosFin 57) f1387 := by
  apply lratCheckerSound f1387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1387
  · intro a ha; simp [p1387] at ha; subst a; trivial
  · exact checked1387
theorem derived1387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1387 := by
  apply localUnsat_implies_entails f1387 [c1120, c36, c301, c300, c50] c1387 unsat1387 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1388 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨45, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c4, some c259, some c260, some c113, some c112, some c20, some c1351, some c1035, some c326, some c139, some c62, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1388 : lratChecker f1388 p1388 = .success := by decide +kernel
theorem unsat1388 : Unsatisfiable (PosFin 57) f1388 := by
  apply lratCheckerSound f1388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1388
  · intro a ha; simp [p1388] at ha; subst a; trivial
  · exact checked1388
theorem derived1388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1388 := by
  apply localUnsat_implies_entails f1388 [c185, c4, c259, c260, c113, c112, c20, c1351, c1035, c326, c139, c62] c1388 unsat1388 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1351 := derived1351 a h
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1389 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1031, some c4, some c102, some c5, some c1383, some c100, some c377, some c1386, some c1387, some c69, some c179, some c372, some c365, some c374, some c163, some c353, some c370, some c1276, some c1388, some c234, some c560, some c20, some c1351, some c326, some c62, some c134, some c139, some c209, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1389 : lratChecker f1389 p1389 = .success := by decide +kernel
theorem unsat1389 : Unsatisfiable (PosFin 57) f1389 := by
  apply lratCheckerSound f1389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1389
  · intro a ha; simp [p1389] at ha; subst a; trivial
  · exact checked1389
theorem derived1389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1389 := by
  apply localUnsat_implies_entails f1389 [c1031, c4, c102, c5, c1383, c100, c377, c1386, c1387, c69, c179, c372, c365, c374, c163, c353, c370, c1276, c1388, c234, c560, c20, c1351, c326, c62, c134, c139, c209] c1389 unsat1389 (by rfl) a
  have h0 : Entails.eval a c1031 := derived1031 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1383 := derived1383 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c1386 := derived1386 a h
  have h8 : Entails.eval a c1387 := derived1387 a h
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c370 := h 369 (by decide)
  have h17 : Entails.eval a c1276 := derived1276 a h
  have h18 : Entails.eval a c1388 := derived1388 a h
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c560 := derived560 a h
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c1351 := derived1351 a h
  have h23 : Entails.eval a c326 := h 325 (by decide)
  have h24 : Entails.eval a c62 := h 61 (by decide)
  have h25 : Entails.eval a c134 := h 133 (by decide)
  have h26 : Entails.eval a c139 := h 138 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1390 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c1383, some c100, some c102, some c4, some c1389, some c94, some c96, some c1325, some c841, some c175, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1390 : lratChecker f1390 p1390 = .success := by decide +kernel
theorem unsat1390 : Unsatisfiable (PosFin 57) f1390 := by
  apply lratCheckerSound f1390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1390
  · intro a ha; simp [p1390] at ha; subst a; trivial
  · exact checked1390
theorem derived1390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1390 := by
  apply localUnsat_implies_entails f1390 [c5, c1383, c100, c102, c4, c1389, c94, c96, c1325, c841, c175] c1390 unsat1390 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1389 := derived1389 a h
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1325 := derived1325 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1391 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c734, some c81, some c68, some c377, some c1357, some c1300, some c2, some c95, some c1276, some c374, some c370, some c353, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1391 : lratChecker f1391 p1391 = .success := by decide +kernel
theorem unsat1391 : Unsatisfiable (PosFin 57) f1391 := by
  apply lratCheckerSound f1391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1391
  · intro a ha; simp [p1391] at ha; subst a; trivial
  · exact checked1391
theorem derived1391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1391 := by
  apply localUnsat_implies_entails f1391 [c734, c81, c68, c377, c1357, c1300, c2, c95, c1276, c374, c370, c353] c1391 unsat1391 (by rfl) a
  have h0 : Entails.eval a c734 := derived734 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c1300 := derived1300 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c1276 := derived1276 a h
  have h9 : Entails.eval a c374 := h 373 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1392 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c68, some c1383, some c5, some c1390, some c1391, some c1274, some c182, some c2, some c1323, some c94, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1392 : lratChecker f1392 p1392 = .success := by decide +kernel
theorem unsat1392 : Unsatisfiable (PosFin 57) f1392 := by
  apply lratCheckerSound f1392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1392
  · intro a ha; simp [p1392] at ha; subst a; trivial
  · exact checked1392
theorem derived1392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1392 := by
  apply localUnsat_implies_entails f1392 [c100, c68, c1383, c5, c1390, c1391, c1274, c182, c2, c1323, c94] c1392 unsat1392 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1390 := derived1390 a h
  have h5 : Entails.eval a c1391 := derived1391 a h
  have h6 : Entails.eval a c1274 := derived1274 a h
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1323 := derived1323 a h
  have h10 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1393 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c1387, some c172, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1393 : lratChecker f1393 p1393 = .success := by decide +kernel
theorem unsat1393 : Unsatisfiable (PosFin 57) f1393 := by
  apply lratCheckerSound f1393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1393
  · intro a ha; simp [p1393] at ha; subst a; trivial
  · exact checked1393
theorem derived1393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1393 := by
  apply localUnsat_implies_entails f1393 [c377, c1387, c172] c1393 unsat1393 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1394 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c48, some c36, some c302, some c340, some c37, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1394 : lratChecker f1394 p1394 = .success := by decide +kernel
theorem unsat1394 : Unsatisfiable (PosFin 57) f1394 := by
  apply lratCheckerSound f1394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1394
  · intro a ha; simp [p1394] at ha; subst a; trivial
  · exact checked1394
theorem derived1394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1394 := by
  apply localUnsat_implies_entails f1394 [c583, c48, c36, c302, c340, c37] c1394 unsat1394 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c340 := h 339 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1395 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c100, some c102, some c1393, some c931, some c94, some c1394, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1395 : lratChecker f1395 p1395 = .success := by decide +kernel
theorem unsat1395 : Unsatisfiable (PosFin 57) f1395 := by
  apply lratCheckerSound f1395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1395
  · intro a ha; simp [p1395] at ha; subst a; trivial
  · exact checked1395
theorem derived1395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1395 := by
  apply localUnsat_implies_entails f1395 [c1383, c100, c102, c1393, c931, c94, c1394] c1395 unsat1395 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c931 := derived931 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1396 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c340, some c37, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1396 : lratChecker f1396 p1396 = .success := by decide +kernel
theorem unsat1396 : Unsatisfiable (PosFin 57) f1396 := by
  apply lratCheckerSound f1396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1396
  · intro a ha; simp [p1396] at ha; subst a; trivial
  · exact checked1396
theorem derived1396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1396 := by
  apply localUnsat_implies_entails f1396 [c300, c340, c37] c1396 unsat1396 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1397 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c100, some c68, some c1392, some c1395, some c1253, some c1266, some c1396, some c95, some c69, some c172, some c841, some c372, some c376, some c377, some c96, some c151, some c1268, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1397 : lratChecker f1397 p1397 = .success := by decide +kernel
theorem unsat1397 : Unsatisfiable (PosFin 57) f1397 := by
  apply lratCheckerSound f1397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1397
  · intro a ha; simp [p1397] at ha; subst a; trivial
  · exact checked1397
theorem derived1397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1397 := by
  apply localUnsat_implies_entails f1397 [c1383, c100, c68, c1392, c1395, c1253, c1266, c1396, c95, c69, c172, c841, c372, c376, c377, c96, c151, c1268] c1397 unsat1397 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c1392 := derived1392 a h
  have h4 : Entails.eval a c1395 := derived1395 a h
  have h5 : Entails.eval a c1253 := derived1253 a h
  have h6 : Entails.eval a c1266 := derived1266 a h
  have h7 : Entails.eval a c1396 := derived1396 a h
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c1268 := derived1268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1398 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c102, some c1397, some c100, some c5, some c1390, some c1326, some c92, some c1325, some c841, some c179, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1398 : lratChecker f1398 p1398 = .success := by decide +kernel
theorem unsat1398 : Unsatisfiable (PosFin 57) f1398 := by
  apply lratCheckerSound f1398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1398
  · intro a ha; simp [p1398] at ha; subst a; trivial
  · exact checked1398
theorem derived1398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1398 := by
  apply localUnsat_implies_entails f1398 [c4, c102, c1397, c100, c5, c1390, c1326, c92, c1325, c841, c179] c1398 unsat1398 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c1397 := derived1397 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1390 := derived1390 a h
  have h6 : Entails.eval a c1326 := derived1326 a h
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c1325 := derived1325 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1399 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1397, some c100, some c102, some c4, some c1398, some c1245, some c1307, some c1395, some c151, some c92, some c1325, some c841, some c179, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c1397, c100, c102, c4, c1398, c1245, c1307, c1395, c151, c92, c1325, c841, c179] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c1397 := derived1397 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c1398 := derived1398 a h
  have h5 : Entails.eval a c1245 := derived1245 a h
  have h6 : Entails.eval a c1307 := derived1307 a h
  have h7 : Entails.eval a c1395 := derived1395 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c1325 := derived1325 a h
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨44, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1324, some c1275, some c2, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c1324, c1275, c2] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c1324 := derived1324 a h
  have h1 : Entails.eval a c1275 := derived1275 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c100, some c1397, some c1399, some c1251, some c1400, some c5, some c1268, some c1393, some c94, some c96, some c1394, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c1383, c100, c1397, c1399, c1251, c1400, c5, c1268, c1393, c94, c96, c1394] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1397 := derived1397 a h
  have h3 : Entails.eval a c1399 := derived1399 a h
  have h4 : Entails.eval a c1251 := derived1251 a h
  have h5 : Entails.eval a c1400 := derived1400 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1268 := derived1268 a h
  have h8 : Entails.eval a c1393 := derived1393 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1401, some c71, some c841, some c100, some c80, some c102, some c4, some c179, some c1325, some c1118, some c5, some c1307, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1401, c71, c841, c100, c80, c102, c4, c179, c1325, c1118, c5, c1307] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1401 := derived1401 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c1325 := derived1325 a h
  have h9 : Entails.eval a c1118 := derived1118 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c1307 := derived1307 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c100, some c1401, some c71, some c841, some c1402, some c1251, some c95, some c1394, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c1383, c100, c1401, c71, c841, c1402, c1251, c95, c1394] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1401 := derived1401 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c1402 := derived1402 a h
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c51, some c300, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c49, c51, c300] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨51, by decide⟩, true), (⟨47, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c151, some c1132, some c231, some c111, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c5, c151, c1132, c231, c111] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c1132 := derived1132 a h
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c81, some c367, some c68, some c379, some c1007, some c328, some c1404, some c382, some c288, some c195, some c236, some c1405, some c160, some c150, some c372, some c234, some c377, some c354, some c115, some c373, some c182, some c180, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c100, c81, c367, c68, c379, c1007, c328, c1404, c382, c288, c195, c236, c1405, c160, c150, c372, c234, c377, c354, c115, c373, c182, c180] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c1007 := derived1007 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c1404 := derived1404 a h
  have h8 : Entails.eval a c382 := derived382 a h
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c1405 := derived1405 a h
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c372 := h 371 (by decide)
  have h16 : Entails.eval a c234 := h 233 (by decide)
  have h17 : Entails.eval a c377 := h 376 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c115 := h 114 (by decide)
  have h20 : Entails.eval a c373 := h 372 (by decide)
  have h21 : Entails.eval a c182 := h 181 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨42, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨56, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c228, some c251, some c236, some c1385, some c326, some c213, some c220, some c139, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c115, c228, c251, c236, c1385, c326, c213, c220, c139] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c236 := h 235 (by decide)
  have h4 : Entails.eval a c1385 := derived1385 a h
  have h5 : Entails.eval a c326 := h 325 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c297, some c301, some c202, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c297, c301, c202] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c297 := h 296 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨56, by decide⟩, false), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c372, some c151, some c376, some c81, some c367, some c374, some c353, some c370, some c1276, some c182, some c185, some c1407, some c234, some c112, some c245, some c249, some c111, some c228, some c1408, some c49, some c288, some c280, some c201, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c68, c372, c151, c376, c81, c367, c374, c353, c370, c1276, c182, c185, c1407, c234, c112, c245, c249, c111, c228, c1408, c49, c288, c280, c201] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c1276 := derived1276 a h
  have h10 : Entails.eval a c182 := h 181 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c1407 := derived1407 a h
  have h13 : Entails.eval a c234 := h 233 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c245 := h 244 (by decide)
  have h16 : Entails.eval a c249 := h 248 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c1408 := derived1408 a h
  have h20 : Entails.eval a c49 := h 48 (by decide)
  have h21 : Entails.eval a c288 := h 287 (by decide)
  have h22 : Entails.eval a c280 := h 279 (by decide)
  have h23 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c178, some c2, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c94, c178, c2] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c68, some c1403, some c3, some c99, some c1383, some c1406, some c95, some c69, some c1410, some c377, some c172, some c5, some c1409, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c100, c68, c1403, c3, c99, c1383, c1406, c95, c69, c1410, c377, c172, c5, c1409] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c1403 := derived1403 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1383 := derived1383 a h
  have h6 : Entails.eval a c1406 := derived1406 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c1410 := derived1410 a h
  have h10 : Entails.eval a c377 := h 376 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c1409 := derived1409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1403, some c3, some c99, some c1383, some c100, some c68, some c81, some c1411, some c155, some c841, some c95, some c379, some c1118, some c5, some c161, some c370, some c168, some c2, some c1387, some c70, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1403, c3, c99, c1383, c100, c68, c81, c1411, c155, c841, c95, c379, c1118, c5, c161, c370, c168, c2, c1387, c70] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1403 := derived1403 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c1411 := derived1411 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c1387 := derived1387 a h
  have h19 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c1383, some c100, some c379, some c1007, some c1404, some c1138, some c328, some c288, some c195, some c236, some c1405, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c5, c1383, c100, c379, c1007, c1404, c1138, c328, c288, c195, c236, c1405] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c1007 := derived1007 a h
  have h5 : Entails.eval a c1404 := derived1404 a h
  have h6 : Entails.eval a c1138 := derived1138 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c1405 := derived1405 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c365, some c83, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 57) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c367, c365, c83] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1403, some c99, some c1414, some c1412, some c3, some c100, some c5, some c1413, some c93, some c841, some c176, some c185, some c1269, some c180, some c369, some c378, some c374, some c353, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 57) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c1383, c1403, c99, c1414, c1412, c3, c100, c5, c1413, c93, c841, c176, c185, c1269, c180, c369, c378, c374, c353] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1403 := derived1403 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c1412 := derived1412 a h
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c1413 := derived1413 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c1269 := derived1269 a h
  have h14 : Entails.eval a c180 := h 179 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c378 := h 377 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨41, by decide⟩, true), (⟨53, by decide⟩, false), (⟨44, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c379, some c354, some c373, some c173, some c377, some c180, some c358, some c2, some c369, some c1123, some c160, some c36, some c324, some c325, some c62, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 57) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1245, c379, c354, c373, c173, c377, c180, c358, c2, c369, c1123, c160, c36, c324, c325, c62] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c1123 := derived1123 a h
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c325 := h 324 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c50, some c751, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 57) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c38, c50, c751] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c751 := derived751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1412, some c1403, some c3, some c99, some c1383, some c100, some c1414, some c1415, some c1416, some c93, some c841, some c173, some c1248, some c180, some c2, some c70, some c369, some c160, some c1417, some c285, some c36, some c324, some c325, some c62, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 57) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c1412, c1403, c3, c99, c1383, c100, c1414, c1415, c1416, c93, c841, c173, c1248, c180, c2, c70, c369, c160, c1417, c285, c36, c324, c325, c62] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1403 := derived1403 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1383 := derived1383 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1414 := derived1414 a h
  have h7 : Entails.eval a c1415 := derived1415 a h
  have h8 : Entails.eval a c1416 := derived1416 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c1248 := derived1248 a h
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c1417 := derived1417 a h
  have h19 : Entails.eval a c285 := h 284 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1412, some c1403, some c3, some c99, some c1383, some c100, some c1418, some c1117, some c155, some c841, some c380, some c93, some c1118, some c1007, some c1404, some c5, some c161, some c1416, some c1256, some c280, some c316, some c276, some c261, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 57) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1412, c1403, c3, c99, c1383, c100, c1418, c1117, c155, c841, c380, c93, c1118, c1007, c1404, c5, c161, c1416, c1256, c280, c316, c276, c261] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1403 := derived1403 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1383 := derived1383 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1418 := derived1418 a h
  have h7 : Entails.eval a c1117 := derived1117 a h
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c1118 := derived1118 a h
  have h13 : Entails.eval a c1007 := derived1007 a h
  have h14 : Entails.eval a c1404 := derived1404 a h
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c1416 := derived1416 a h
  have h18 : Entails.eval a c1256 := derived1256 a h
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c316 := h 315 (by decide)
  have h21 : Entails.eval a c276 := h 275 (by decide)
  have h22 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1403, some c99, some c3, some c1412, some c1419, some c95, some c69, some c1410, some c841, some c371, some c378, some c374, some c155, some c172, some c1414, some c5, some c353, some c369, some c1269, some c182, some c185, some c163, some c1407, some c232, some c234, some c112, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 57) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c1383, c1403, c99, c3, c1412, c1419, c95, c69, c1410, c841, c371, c378, c374, c155, c172, c1414, c5, c353, c369, c1269, c182, c185, c163, c1407, c232, c234, c112] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1403 := derived1403 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1412 := derived1412 a h
  have h5 : Entails.eval a c1419 := derived1419 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c1410 := derived1410 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c374 := h 373 (by decide)
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c1414 := derived1414 a h
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c1269 := derived1269 a h
  have h20 : Entails.eval a c182 := h 181 (by decide)
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c1407 := derived1407 a h
  have h24 : Entails.eval a c232 := h 231 (by decide)
  have h25 : Entails.eval a c234 := h 233 (by decide)
  have h26 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c102, some c1420, some c1383, some c100, some c80, some c68, some c1395, some c5, some c8, some c1362, some c1376, some c153, some c185, some c1387, some c1274, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 57) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c99, c102, c1420, c1383, c100, c80, c68, c1395, c5, c8, c1362, c1376, c153, c185, c1387, c1274] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c1420 := derived1420 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c1395 := derived1395 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c1362 := derived1362 a h
  have h11 : Entails.eval a c1376 := derived1376 a h
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c1387 := derived1387 a h
  have h15 : Entails.eval a c1274 := derived1274 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1421, some c99, some c102, some c1420, some c100, some c1331, some c5, some c1245, some c1395, some c1313, some c92, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 57) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c1421, c99, c102, c1420, c100, c1331, c5, c1245, c1395, c1313, c92] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c1421 := derived1421 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c1420 := derived1420 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1331 := derived1331 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c1245 := derived1245 a h
  have h8 : Entails.eval a c1395 := derived1395 a h
  have h9 : Entails.eval a c1313 := derived1313 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c1314, some c37, some c60, some c326, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 57) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c284, c1314, c37, c60, c326] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c1314 := derived1314 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1423, some c48, some c36, some c286, some c324, some c37, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 57) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1423, c48, c36, c286, c324, c37] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1423 := derived1423 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1362, some c365, some c5, some c157, some c1424, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 57) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c100, c1362, c365, c5, c157, c1424] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1362 := derived1362 a h
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c1424 := derived1424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1420, some c1383, some c100, some c102, some c99, some c1421, some c1422, some c69, some c1425, some c71, some c946, some c84, some c841, some c369, some c179, some c8, some c1088, some c161, some c148, some c196, some c132, some c48, some c52, some c285, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 57) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1420, c1383, c100, c102, c99, c1421, c1422, c69, c1425, c71, c946, c84, c841, c369, c179, c8, c1088, c161, c148, c196, c132, c48, c52, c285] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1420 := derived1420 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1421 := derived1421 a h
  have h6 : Entails.eval a c1422 := derived1422 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c1425 := derived1425 a h
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c946 := derived946 a h
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c179 := h 178 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c1088 := derived1088 a h
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c196 := h 195 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  have h21 : Entails.eval a c48 := h 47 (by decide)
  have h22 : Entails.eval a c52 := h 51 (by decide)
  have h23 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1426, some c1420, some c1383, some c1414, some c328, some c382, some c288, some c157, some c39, some c195, some c5, some c27, some c19, some c106, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 57) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c1426, c1420, c1383, c1414, c328, c382, c288, c157, c39, c195, c5, c27, c19, c106] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c1426 := derived1426 a h
  have h1 : Entails.eval a c1420 := derived1420 a h
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨44, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1426, some c81, some c68, some c1420, some c1383, some c379, some c1007, some c1404, some c1427, some c80, some c1118, some c5, some c11, some c161, some c155, some c320, some c280, some c373, some c149, some c316, some c276, some c261, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 57) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c100, c1426, c81, c68, c1420, c1383, c379, c1007, c1404, c1427, c80, c1118, c5, c11, c161, c155, c320, c280, c373, c149, c316, c276, c261] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1426 := derived1426 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c1420 := derived1420 a h
  have h5 : Entails.eval a c1383 := derived1383 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c1007 := derived1007 a h
  have h8 : Entails.eval a c1404 := derived1404 a h
  have h9 : Entails.eval a c1427 := derived1427 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c149 := h 148 (by decide)
  have h20 : Entails.eval a c316 := h 315 (by decide)
  have h21 : Entails.eval a c276 := h 275 (by decide)
  have h22 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c95, some c1414, some c372, some c1362, some c149, some c5, some c374, some c172, some c157, some c376, some c370, some c358, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 57) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c69, c95, c1414, c372, c1362, c149, c5, c374, c172, c157, c376, c370, c358] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c1414 := derived1414 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c1362 := derived1362 a h
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c343, some c341, some c61, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 57) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c343, c341, c61] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c343 := h 342 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c303, some c49, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 57) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c301, c303, c49] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1426, some c1420, some c1383, some c100, some c68, some c81, some c1428, some c95, some c69, some c841, some c1429, some c80, some c155, some c11, some c1118, some c376, some c172, some c357, some c370, some c1039, some c364, some c149, some c1430, some c1431, some c194, some c38, some c18, some c249, some c23, some c7, some c106, some c107, some c162, some c1006, some c230, some c209, some c212, some c313, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 57) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c1426, c1420, c1383, c100, c68, c81, c1428, c95, c69, c841, c1429, c80, c155, c11, c1118, c376, c172, c357, c370, c1039, c364, c149, c1430, c1431, c194, c38, c18, c249, c23, c7, c106, c107, c162, c1006, c230, c209, c212, c313] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c1426 := derived1426 a h
  have h1 : Entails.eval a c1420 := derived1420 a h
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c1428 := derived1428 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c1429 := derived1429 a h
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c1118 := derived1118 a h
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c357 := h 356 (by decide)
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c1039 := derived1039 a h
  have h20 : Entails.eval a c364 := h 363 (by decide)
  have h21 : Entails.eval a c149 := h 148 (by decide)
  have h22 : Entails.eval a c1430 := derived1430 a h
  have h23 : Entails.eval a c1431 := derived1431 a h
  have h24 : Entails.eval a c194 := h 193 (by decide)
  have h25 : Entails.eval a c38 := h 37 (by decide)
  have h26 : Entails.eval a c18 := h 17 (by decide)
  have h27 : Entails.eval a c249 := h 248 (by decide)
  have h28 : Entails.eval a c23 := h 22 (by decide)
  have h29 : Entails.eval a c7 := h 6 (by decide)
  have h30 : Entails.eval a c106 := h 105 (by decide)
  have h31 : Entails.eval a c107 := h 106 (by decide)
  have h32 : Entails.eval a c162 := h 161 (by decide)
  have h33 : Entails.eval a c1006 := derived1006 a h
  have h34 : Entails.eval a c230 := h 229 (by decide)
  have h35 : Entails.eval a c209 := h 208 (by decide)
  have h36 : Entails.eval a c212 := h 211 (by decide)
  have h37 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1426, some c1383, some c100, some c1007, some c1404, some c1427, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 57) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1426, c1383, c100, c1007, c1404, c1427] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1426 := derived1426 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c1007 := derived1007 a h
  have h4 : Entails.eval a c1404 := derived1404 a h
  have h5 : Entails.eval a c1427 := derived1427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1420, some c1383, some c1426, some c1414, some c149, some c1432, some c100, some c5, some c1362, some c83, some c1433, some c93, some c1079, some c1078, some c189, some c240, some c237, some c115, some c186, some c1269, some c114, some c1247, some c18, some c1417, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 57) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c1420, c1383, c1426, c1414, c149, c1432, c100, c5, c1362, c83, c1433, c93, c1079, c1078, c189, c240, c237, c115, c186, c1269, c114, c1247, c18, c1417] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c1420 := derived1420 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1426 := derived1426 a h
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c1432 := derived1432 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c1362 := derived1362 a h
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c1433 := derived1433 a h
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c1079 := derived1079 a h
  have h13 : Entails.eval a c1078 := derived1078 a h
  have h14 : Entails.eval a c189 := h 188 (by decide)
  have h15 : Entails.eval a c240 := h 239 (by decide)
  have h16 : Entails.eval a c237 := h 236 (by decide)
  have h17 : Entails.eval a c115 := h 114 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c1269 := derived1269 a h
  have h20 : Entails.eval a c114 := h 113 (by decide)
  have h21 : Entails.eval a c1247 := derived1247 a h
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c1417 := derived1417 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1420, some c1383, some c1426, some c1414, some c1434, some c157, some c369, some c1245, some c149, some c379, some c1433, some c358, some c72, some c374, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 57) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c1432, c1420, c1383, c1426, c1414, c1434, c157, c369, c1245, c149, c379, c1433, c358, c72, c374] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1420 := derived1420 a h
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c1426 := derived1426 a h
  have h4 : Entails.eval a c1414 := derived1414 a h
  have h5 : Entails.eval a c1434 := derived1434 a h
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c1245 := derived1245 a h
  have h9 : Entails.eval a c149 := h 148 (by decide)
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c1433 := derived1433 a h
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1426, some c1420, some c1383, some c100, some c1414, some c149, some c373, some c1434, some c1245, some c157, some c158, some c369, some c1435, some c92, some c93, some c11, some c374, some c1079, some c1078, some c180, some c358, some c70, some c189, some c18, some c240, some c237, some c108, some c115, some c1069, some c21, some c338, some c215, some c214, some c147, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 57) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c1432, c1426, c1420, c1383, c100, c1414, c149, c373, c1434, c1245, c157, c158, c369, c1435, c92, c93, c11, c374, c1079, c1078, c180, c358, c70, c189, c18, c240, c237, c108, c115, c1069, c21, c338, c215, c214, c147] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1426 := derived1426 a h
  have h2 : Entails.eval a c1420 := derived1420 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1414 := derived1414 a h
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c373 := h 372 (by decide)
  have h8 : Entails.eval a c1434 := derived1434 a h
  have h9 : Entails.eval a c1245 := derived1245 a h
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c1435 := derived1435 a h
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c93 := h 92 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c1079 := derived1079 a h
  have h19 : Entails.eval a c1078 := derived1078 a h
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c70 := h 69 (by decide)
  have h23 : Entails.eval a c189 := h 188 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c240 := h 239 (by decide)
  have h26 : Entails.eval a c237 := h 236 (by decide)
  have h27 : Entails.eval a c108 := h 107 (by decide)
  have h28 : Entails.eval a c115 := h 114 (by decide)
  have h29 : Entails.eval a c1069 := derived1069 a h
  have h30 : Entails.eval a c21 := h 20 (by decide)
  have h31 : Entails.eval a c338 := h 337 (by decide)
  have h32 : Entails.eval a c215 := h 214 (by decide)
  have h33 : Entails.eval a c214 := h 213 (by decide)
  have h34 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c71, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 57) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1394, c71] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1438 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c379, some c1118, some c5, some c1245, some c1437, some c11, some c161, some c155, some c841, some c373, some c956, some c169, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 57) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c100, c379, c1118, c5, c1245, c1437, c11, c161, c155, c841, c373, c956, c169] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1245 := derived1245 a h
  have h5 : Entails.eval a c1437 := derived1437 a h
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c373 := h 372 (by decide)
  have h11 : Entails.eval a c956 := derived956 a h
  have h12 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1269, some c1039, some c185, some c171, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 57) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1269, c1039, c185, c171] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1269 := derived1269 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1420, some c1432, some c1436, some c1383, some c1438, some c100, some c1426, some c93, some c1251, some c841, some c155, some c11, some c1439, some c1247, some c366, some c1417, some c149, some c7, some c1079, some c1078, some c189, some c237, some c18, some c114, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 57) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c1420, c1432, c1436, c1383, c1438, c100, c1426, c93, c1251, c841, c155, c11, c1439, c1247, c366, c1417, c149, c7, c1079, c1078, c189, c237, c18, c114] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c1420 := derived1420 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1436 := derived1436 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c1438 := derived1438 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1426 := derived1426 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c1251 := derived1251 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1439 := derived1439 a h
  have h13 : Entails.eval a c1247 := derived1247 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c1417 := derived1417 a h
  have h16 : Entails.eval a c149 := h 148 (by decide)
  have h17 : Entails.eval a c7 := h 6 (by decide)
  have h18 : Entails.eval a c1079 := derived1079 a h
  have h19 : Entails.eval a c1078 := derived1078 a h
  have h20 : Entails.eval a c189 := h 188 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1417, some c285, some c36, some c324, some c325, some c62, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 57) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1417, c285, c36, c324, c325, c62] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1417 := derived1417 a h
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1442 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c122, some c418, some c37, some c132, some c324, some c61, some c148, some c336, some c265, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 57) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c284, c122, c418, c37, c132, c324, c61, c148, c336, c265] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1443 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1440, some c100, some c1426, some c1383, some c1420, some c1432, some c1436, some c1438, some c1251, some c93, some c841, some c155, some c11, some c83, some c371, some c163, some c1439, some c369, some c357, some c1442, some c49, some c36, some c920, some c132, some c324, some c138, some c63, some c148, some c265, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 57) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c1440, c100, c1426, c1383, c1420, c1432, c1436, c1438, c1251, c93, c841, c155, c11, c83, c371, c163, c1439, c369, c357, c1442, c49, c36, c920, c132, c324, c138, c63, c148, c265] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1426 := derived1426 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c1420 := derived1420 a h
  have h5 : Entails.eval a c1432 := derived1432 a h
  have h6 : Entails.eval a c1436 := derived1436 a h
  have h7 : Entails.eval a c1438 := derived1438 a h
  have h8 : Entails.eval a c1251 := derived1251 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c155 := h 154 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c1439 := derived1439 a h
  have h17 : Entails.eval a c369 := h 368 (by decide)
  have h18 : Entails.eval a c357 := h 356 (by decide)
  have h19 : Entails.eval a c1442 := derived1442 a h
  have h20 : Entails.eval a c49 := h 48 (by decide)
  have h21 : Entails.eval a c36 := h 35 (by decide)
  have h22 : Entails.eval a c920 := derived920 a h
  have h23 : Entails.eval a c132 := h 131 (by decide)
  have h24 : Entails.eval a c324 := h 323 (by decide)
  have h25 : Entails.eval a c138 := h 137 (by decide)
  have h26 : Entails.eval a c63 := h 62 (by decide)
  have h27 : Entails.eval a c148 := h 147 (by decide)
  have h28 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1426, some c1383, some c1420, some c1432, some c1436, some c1438, some c1251, some c93, some c841, some c155, some c11, some c1439, some c1440, some c83, some c371, some c158, some c163, some c186, some c1441, some c1443, some c171, some c1079, some c1078, some c189, some c221, some c18, some c114, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 57) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c100, c1426, c1383, c1420, c1432, c1436, c1438, c1251, c93, c841, c155, c11, c1439, c1440, c83, c371, c158, c163, c186, c1441, c1443, c171, c1079, c1078, c189, c221, c18, c114] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1426 := derived1426 a h
  have h2 : Entails.eval a c1383 := derived1383 a h
  have h3 : Entails.eval a c1420 := derived1420 a h
  have h4 : Entails.eval a c1432 := derived1432 a h
  have h5 : Entails.eval a c1436 := derived1436 a h
  have h6 : Entails.eval a c1438 := derived1438 a h
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1439 := derived1439 a h
  have h13 : Entails.eval a c1440 := derived1440 a h
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c1441 := derived1441 a h
  have h20 : Entails.eval a c1443 := derived1443 a h
  have h21 : Entails.eval a c171 := h 170 (by decide)
  have h22 : Entails.eval a c1079 := derived1079 a h
  have h23 : Entails.eval a c1078 := derived1078 a h
  have h24 : Entails.eval a c189 := h 188 (by decide)
  have h25 : Entails.eval a c221 := h 220 (by decide)
  have h26 : Entails.eval a c18 := h 17 (by decide)
  have h27 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨10, by decide⟩, true), (⟨56, by decide⟩, false), (⟨47, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c980, some c1039, some c169, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 57) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c980, c1039, c169] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c980 := derived980 a h
  have h1 : Entails.eval a c1039 := derived1039 a h
  have h2 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c418, some c37, some c296, some c132, some c324, some c61, some c148, some c336, some c265, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 57) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c418, c37, c296, c132, c324, c61, c148, c336, c265] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c418 := derived418 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1426, some c1420, some c1383, some c100, some c1436, some c1438, some c93, some c1251, some c841, some c155, some c11, some c1444, some c1245, some c158, some c1445, some c369, some c366, some c160, some c150, some c163, some c1446, some c273, some c284, some c49, some c36, some c296, some c132, some c324, some c591, some c63, some c148, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 57) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1432, c1426, c1420, c1383, c100, c1436, c1438, c93, c1251, c841, c155, c11, c1444, c1245, c158, c1445, c369, c366, c160, c150, c163, c1446, c273, c284, c49, c36, c296, c132, c324, c591, c63, c148] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1426 := derived1426 a h
  have h2 : Entails.eval a c1420 := derived1420 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1436 := derived1436 a h
  have h6 : Entails.eval a c1438 := derived1438 a h
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c1251 := derived1251 a h
  have h9 : Entails.eval a c841 := derived841 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1444 := derived1444 a h
  have h13 : Entails.eval a c1245 := derived1245 a h
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c1445 := derived1445 a h
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c366 := h 365 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c150 := h 149 (by decide)
  have h20 : Entails.eval a c163 := h 162 (by decide)
  have h21 : Entails.eval a c1446 := derived1446 a h
  have h22 : Entails.eval a c273 := h 272 (by decide)
  have h23 : Entails.eval a c284 := h 283 (by decide)
  have h24 : Entails.eval a c49 := h 48 (by decide)
  have h25 : Entails.eval a c36 := h 35 (by decide)
  have h26 : Entails.eval a c296 := h 295 (by decide)
  have h27 : Entails.eval a c132 := h 131 (by decide)
  have h28 : Entails.eval a c324 := h 323 (by decide)
  have h29 : Entails.eval a c591 := derived591 a h
  have h30 : Entails.eval a c63 := h 62 (by decide)
  have h31 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, false), (⟨45, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c278, some c284, some c1314, some c418, some c61, some c292, some c332, some c336, some c261, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 57) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c278, c284, c1314, c418, c61, c292, c332, c336, c261] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c278 := h 277 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c1314 := derived1314 a h
  have h3 : Entails.eval a c418 := derived418 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1447, some c69, some c1426, some c95, some c1432, some c1420, some c100, some c1414, some c1425, some c1362, some c149, some c5, some c172, some c157, some c1448, some c49, some c36, some c292, some c296, some c324, some c318, some c261, some c63, some c332, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 57) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1383, c1447, c69, c1426, c95, c1432, c1420, c100, c1414, c1425, c1362, c149, c5, c172, c157, c1448, c49, c36, c292, c296, c324, c318, c261, c63, c332] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1447 := derived1447 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c1426 := derived1426 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c1432 := derived1432 a h
  have h6 : Entails.eval a c1420 := derived1420 a h
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1425 := derived1425 a h
  have h10 : Entails.eval a c1362 := derived1362 a h
  have h11 : Entails.eval a c149 := h 148 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c172 := h 171 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c1448 := derived1448 a h
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c292 := h 291 (by decide)
  have h19 : Entails.eval a c296 := h 295 (by decide)
  have h20 : Entails.eval a c324 := h 323 (by decide)
  have h21 : Entails.eval a c318 := h 317 (by decide)
  have h22 : Entails.eval a c261 := h 260 (by decide)
  have h23 : Entails.eval a c63 := h 62 (by decide)
  have h24 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1118, some c841, some c376, some c357, some c369, some c1269, some c364, some c7, some c1430, some c1431, some c38, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 57) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c1118, c841, c376, c357, c369, c1269, c364, c7, c1430, c1431, c38] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c1118 := derived1118 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c1269 := derived1269 a h
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c1430 := derived1430 a h
  have h9 : Entails.eval a c1431 := derived1431 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c841, some c1450, some c1439, some c369, some c366, some c357, some c163, some c1248, some c186, some c178, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 57) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c158, c841, c1450, c1439, c369, c366, c357, c163, c1248, c186, c178] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c1439 := derived1439 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c1248 := derived1248 a h
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c100, some c1420, some c1426, some c1432, some c1447, some c95, some c69, some c841, some c371, some c1449, some c71, some c155, some c11, some c158, some c1451, some c172, some c1445, some c366, some c163, some c1446, some c273, some c284, some c49, some c36, some c296, some c132, some c324, some c591, some c63, some c148, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 57) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1383, c100, c1420, c1426, c1432, c1447, c95, c69, c841, c371, c1449, c71, c155, c11, c158, c1451, c172, c1445, c366, c163, c1446, c273, c284, c49, c36, c296, c132, c324, c591, c63, c148] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1420 := derived1420 a h
  have h3 : Entails.eval a c1426 := derived1426 a h
  have h4 : Entails.eval a c1432 := derived1432 a h
  have h5 : Entails.eval a c1447 := derived1447 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c1449 := derived1449 a h
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c1451 := derived1451 a h
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c1445 := derived1445 a h
  have h18 : Entails.eval a c366 := h 365 (by decide)
  have h19 : Entails.eval a c163 := h 162 (by decide)
  have h20 : Entails.eval a c1446 := derived1446 a h
  have h21 : Entails.eval a c273 := h 272 (by decide)
  have h22 : Entails.eval a c284 := h 283 (by decide)
  have h23 : Entails.eval a c49 := h 48 (by decide)
  have h24 : Entails.eval a c36 := h 35 (by decide)
  have h25 : Entails.eval a c296 := h 295 (by decide)
  have h26 : Entails.eval a c132 := h 131 (by decide)
  have h27 : Entails.eval a c324 := h 323 (by decide)
  have h28 : Entails.eval a c591 := derived591 a h
  have h29 : Entails.eval a c63 := h 62 (by decide)
  have h30 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c1387, some c1394, some c931, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 57) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c99, c1387, c1394, c931] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c1394 := derived1394 a h
  have h3 : Entails.eval a c931 := derived931 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c50, some c286, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 57) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c52, c50, c286] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c1453, some c69, some c94, some c1454, some c301, some c48, some c36, some c286, some c341, some c37, some c64, some c326, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 57) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c99, c1453, c69, c94, c1454, c301, c48, c36, c286, c341, c37, c64, c326] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c1454 := derived1454 a h
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c92, some c841, some c68, some c4, some c1326, some c177, some c187, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 57) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c99, c92, c841, c68, c4, c1326, c177, c187] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c1326 := derived1326 a h
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c92, some c1325, some c373, some c1456, some c170, some c171, some c187, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 57) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c99, c92, c1325, c373, c1456, c170, c171, c187] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c373 := h 372 (by decide)
  have h4 : Entails.eval a c1456 := derived1456 a h
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨30, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c129, some c162, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 57) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c285, c129, c162] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c102, some c1452, some c1383, some c100, some c1455, some c68, some c92, some c841, some c1457, some c69, some c371, some c1425, some c1454, some c4, some c177, some c187, some c1458, some c48, some c36, some c286, some c324, some c37, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 57) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c99, c102, c1452, c1383, c100, c1455, c68, c92, c841, c1457, c69, c371, c1425, c1454, c4, c177, c187, c1458, c48, c36, c286, c324, c37] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c1452 := derived1452 a h
  have h3 : Entails.eval a c1383 := derived1383 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1455 := derived1455 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c1457 := derived1457 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c1425 := derived1425 a h
  have h13 : Entails.eval a c1454 := derived1454 a h
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c1458 := derived1458 a h
  have h18 : Entails.eval a c48 := h 47 (by decide)
  have h19 : Entails.eval a c36 := h 35 (by decide)
  have h20 : Entails.eval a c286 := h 285 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c1394, some c1457, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 57) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c99, c1394, c1457] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c1394 := derived1394 a h
  have h2 : Entails.eval a c1457 := derived1457 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c52, some c285, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 57) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c48, c52, c285] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨31, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨39, by decide⟩, false), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c150, some c1142, some c5, some c156, some c941, some c1118, some c366, some c353, some c331, some c1341, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 57) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c841, c150, c1142, c5, c156, c941, c1118, c366, c353, c331, c1341] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c150 := h 149 (by decide)
  have h2 : Entails.eval a c1142 := derived1142 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c941 := derived941 a h
  have h6 : Entails.eval a c1118 := derived1118 a h
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c331 := h 330 (by decide)
  have h10 : Entails.eval a c1341 := derived1341 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c325, some c62, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 57) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c324, c325, c62] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1464 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1383, some c100, some c102, some c99, some c1459, some c80, some c71, some c84, some c1460, some c69, some c1463, some c36, some c284, some c285, some c50, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 57) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c1452, c1383, c100, c102, c99, c1459, c80, c71, c84, c1460, c69, c1463, c36, c284, c285, c50] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c1463 := derived1463 a h
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c1404, some c81, some c1387, some c70, some c1417, some c287, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 57) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c68, c1404, c81, c1387, c70, c1417, c287] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c1404 := derived1404 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c1417 := derived1417 a h
  have h6 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c111, some c120, some c136, some c189, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 57) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c106, c111, c120, c136, c189] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1464, some c1414, some c100, some c68, some c81, some c1007, some c1404, some c328, some c288, some c382, some c195, some c39, some c236, some c27, some c19, some c1465, some c1466, some c5, some c157, some c150, some c2, some c377, some c154, some c327, some c287, some c272, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 57) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1383, c1464, c1414, c100, c68, c81, c1007, c1404, c328, c288, c382, c195, c39, c236, c27, c19, c1465, c1466, c5, c157, c150, c2, c377, c154, c327, c287, c272] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1464 := derived1464 a h
  have h2 : Entails.eval a c1414 := derived1414 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c1007 := derived1007 a h
  have h7 : Entails.eval a c1404 := derived1404 a h
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c382 := derived382 a h
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c19 := h 18 (by decide)
  have h16 : Entails.eval a c1465 := derived1465 a h
  have h17 : Entails.eval a c1466 := derived1466 a h
  have h18 : Entails.eval a c5 := h 4 (by decide)
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c377 := h 376 (by decide)
  have h23 : Entails.eval a c154 := h 153 (by decide)
  have h24 : Entails.eval a c327 := h 326 (by decide)
  have h25 : Entails.eval a c287 := h 286 (by decide)
  have h26 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1394, some c1387, some c96, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 57) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c1394, c1387, c96] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c1394 := derived1394 a h
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c288, some c39, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 57) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c328, c288, c39] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1467, some c1383, some c1464, some c1414, some c1452, some c100, some c1251, some c1325, some c1394, some c1007, some c1404, some c1468, some c1469, some c72, some c83, some c371, some c1425, some c354, some c181, some c2, some c374, some c180, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 57) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1467, c1383, c1464, c1414, c1452, c100, c1251, c1325, c1394, c1007, c1404, c1468, c1469, c72, c83, c371, c1425, c354, c181, c2, c374, c180] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1467 := derived1467 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1464 := derived1464 a h
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c1452 := derived1452 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c1394 := derived1394 a h
  have h9 : Entails.eval a c1007 := derived1007 a h
  have h10 : Entails.eval a c1404 := derived1404 a h
  have h11 : Entails.eval a c1468 := derived1468 a h
  have h12 : Entails.eval a c1469 := derived1469 a h
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c1425 := derived1425 a h
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c181 := h 180 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c374 := h 373 (by decide)
  have h21 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1417, some c83, some c1247, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 57) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1441, c1417, c83, c1247] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1417 := derived1417 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c1247 := derived1247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1387, some c70, some c1471, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 57) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1387, c70, c1471] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1387 := derived1387 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c1471 := derived1471 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1383, some c1464, some c1414, some c328, some c288, some c382, some c195, some c236, some c27, some c19, some c1466, some c5, some c157, some c150, some c2, some c377, some c154, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 57) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c1383, c1464, c1414, c328, c288, c382, c195, c236, c27, c19, c1466, c5, c157, c150, c2, c377, c154] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c1383 := derived1383 a h
  have h1 : Entails.eval a c1464 := derived1464 a h
  have h2 : Entails.eval a c1414 := derived1414 a h
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c382 := derived382 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1466 := derived1466 a h
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c1383, some c1464, some c1467, some c1472, some c1404, some c1007, some c379, some c1470, some c1414, some c1473, some c72, some c83, some c371, some c354, some c358, some c374, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 57) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c100, c1383, c1464, c1467, c1472, c1404, c1007, c379, c1470, c1414, c1473, c72, c83, c371, c354, c358, c374] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1464 := derived1464 a h
  have h3 : Entails.eval a c1467 := derived1467 a h
  have h4 : Entails.eval a c1472 := derived1472 a h
  have h5 : Entails.eval a c1404 := derived1404 a h
  have h6 : Entails.eval a c1007 := derived1007 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1470 := derived1470 a h
  have h9 : Entails.eval a c1414 := derived1414 a h
  have h10 : Entails.eval a c1473 := derived1473 a h
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c371 := h 370 (by decide)
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c358 := h 357 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c288, some c1247, some c327, some c272, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 57) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c328, c288, c1247, c327, c272] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c1247 := derived1247 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1467, some c1383, some c1464, some c1414, some c1452, some c100, some c379, some c1007, some c1404, some c1472, some c1474, some c369, some c1475, some c72, some c83, some c841, some c371, some c354, some c151, some c374, some c5, some c188, some c180, some c157, some c2, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 57) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1467, c1383, c1464, c1414, c1452, c100, c379, c1007, c1404, c1472, c1474, c369, c1475, c72, c83, c841, c371, c354, c151, c374, c5, c188, c180, c157, c2] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1467 := derived1467 a h
  have h1 : Entails.eval a c1383 := derived1383 a h
  have h2 : Entails.eval a c1464 := derived1464 a h
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c1452 := derived1452 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c1007 := derived1007 a h
  have h8 : Entails.eval a c1404 := derived1404 a h
  have h9 : Entails.eval a c1472 := derived1472 a h
  have h10 : Entails.eval a c1474 := derived1474 a h
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c1475 := derived1475 a h
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c188 := h 187 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  have h23 : Entails.eval a c157 := h 156 (by decide)
  have h24 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c841, some c1471, some c70, some c82, some c1248, some c374, some c371, some c986, some c176, some c173, some c187, some c185, some c162, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 57) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c93, c841, c1471, c70, c82, c1248, c374, c371, c986, c176, c173, c187, c185, c162] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c1471 := derived1471 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c1248 := derived1248 a h
  have h6 : Entails.eval a c374 := h 373 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c986 := derived986 a h
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c173 := h 172 (by decide)
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨41, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1248, some c374, some c353, some c149, some c368, some c2, some c162, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 57) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c1248, c374, c353, c149, c368, c2, c162] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c1248 := derived1248 a h
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨56, by decide⟩, false), (⟨44, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1464, some c100, some c1478, some c154, some c2, some c7, some c158, some c157, some c368, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 57) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c1464, c100, c1478, c154, c2, c7, c158, c157, c368] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c1464 := derived1464 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c1478 := derived1478 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c187, some c176, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 57) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c188, c187, c176] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived1480

end CochromaticTwenty.Certificates.B16_8_2
