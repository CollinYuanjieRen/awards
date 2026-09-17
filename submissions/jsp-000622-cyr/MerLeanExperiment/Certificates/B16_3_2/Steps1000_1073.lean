import MerLeanExperiment.Certificates.B16_3_2.Steps0900_0999

/-! Generated from the actual pinned b16_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1399 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c55, some c54, some c330, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1399 : lratChecker f1399 p1399 = .success := by decide +kernel
theorem unsat1399 : Unsatisfiable (PosFin 57) f1399 := by
  apply lratCheckerSound f1399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1399
  · intro a ha; simp [p1399] at ha; subst a; trivial
  · exact checked1399
theorem derived1399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1399 := by
  apply localUnsat_implies_entails f1399 [c53, c55, c54, c330] c1399 unsat1399 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1400 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c140, some c298, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1400 : lratChecker f1400 p1400 = .success := by decide +kernel
theorem unsat1400 : Unsatisfiable (PosFin 57) f1400 := by
  apply lratCheckerSound f1400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1400
  · intro a ha; simp [p1400] at ha; subst a; trivial
  · exact checked1400
theorem derived1400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1400 := by
  apply localUnsat_implies_entails f1400 [c132, c140, c298] c1400 unsat1400 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1401 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c35, some c1278, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1401 : lratChecker f1401 p1401 = .success := by decide +kernel
theorem unsat1401 : Unsatisfiable (PosFin 57) f1401 := by
  apply lratCheckerSound f1401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1401
  · intro a ha; simp [p1401] at ha; subst a; trivial
  · exact checked1401
theorem derived1401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1401 := by
  apply localUnsat_implies_entails f1401 [c33, c35, c1278] c1401 unsat1401 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c1278 := derived1278 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1402 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨33, by decide⟩, false), (⟨24, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1396, some c1397, some c1398, some c1399, some c1400, some c1265, some c1382, some c16, some c1401, some c1269, some c1390, some c158, some c937, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1402 : lratChecker f1402 p1402 = .success := by decide +kernel
theorem unsat1402 : Unsatisfiable (PosFin 57) f1402 := by
  apply lratCheckerSound f1402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1402
  · intro a ha; simp [p1402] at ha; subst a; trivial
  · exact checked1402
theorem derived1402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1402 := by
  apply localUnsat_implies_entails f1402 [c1396, c1397, c1398, c1399, c1400, c1265, c1382, c16, c1401, c1269, c1390, c158, c937] c1402 unsat1402 (by rfl) a
  have h0 : Entails.eval a c1396 := derived1396 a h
  have h1 : Entails.eval a c1397 := derived1397 a h
  have h2 : Entails.eval a c1398 := derived1398 a h
  have h3 : Entails.eval a c1399 := derived1399 a h
  have h4 : Entails.eval a c1400 := derived1400 a h
  have h5 : Entails.eval a c1265 := derived1265 a h
  have h6 : Entails.eval a c1382 := derived1382 a h
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c1401 := derived1401 a h
  have h9 : Entails.eval a c1269 := derived1269 a h
  have h10 : Entails.eval a c1390 := derived1390 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c937 := derived937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1403 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c32, some c690, some c43, some c937, some c1029, some c232, some c1281, some c1269, some c1392, some c69, some c49, some c362, some c324, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 57) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c24, c32, c690, c43, c937, c1029, c232, c1281, c1269, c1392, c69, c49, c362, c324] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c690 := derived690 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c1029 := derived1029 a h
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c1281 := derived1281 a h
  have h8 : Entails.eval a c1269 := derived1269 a h
  have h9 : Entails.eval a c1392 := derived1392 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c937, some c158, some c1269, some c1204, some c33, some c329, some c1270, some c171, some c76, some c16, some c363, some c51, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 57) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c937, c158, c1269, c1204, c33, c329, c1270, c171, c76, c16, c363, c51] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c937 := derived937 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c1270 := derived1270 a h
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1269, some c158, some c1387, some c16, some c183, some c1237, some c363, some c131, some c49, some c327, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 57) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1269, c158, c1387, c16, c183, c1237, c363, c131, c49, c327] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1269 := derived1269 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c1237 := derived1237 a h
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1402, some c123, some c1403, some c1380, some c1376, some c1404, some c1269, some c158, some c1405, some c53, some c331, some c228, some c1278, some c36, some c232, some c276, some c282, some c49, some c37, some c226, some c16, some c334, some c131, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 57) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c1402, c123, c1403, c1380, c1376, c1404, c1269, c158, c1405, c53, c331, c228, c1278, c36, c232, c276, c282, c49, c37, c226, c16, c334, c131] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c1402 := derived1402 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c1403 := derived1403 a h
  have h3 : Entails.eval a c1380 := derived1380 a h
  have h4 : Entails.eval a c1376 := derived1376 a h
  have h5 : Entails.eval a c1404 := derived1404 a h
  have h6 : Entails.eval a c1269 := derived1269 a h
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c1405 := derived1405 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c1278 := derived1278 a h
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c276 := h 275 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c37 := h 36 (by decide)
  have h19 : Entails.eval a c226 := h 225 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c334 := h 333 (by decide)
  have h22 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1407 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, false), (⟨5, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c214, some c686, some c193, some c89, some c209, some c71, some c91, some c337, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 57) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c16, c214, c686, c193, c89, c209, c71, c91, c337] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c686 := derived686 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1402, some c123, some c1403, some c1380, some c1376, some c1406, some c25, some c17, some c1381, some c1407, some c195, some c297, some c337, some c159, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 57) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1402, c123, c1403, c1380, c1376, c1406, c25, c17, c1381, c1407, c195, c297, c337, c159] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1402 := derived1402 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c1403 := derived1403 a h
  have h3 : Entails.eval a c1380 := derived1380 a h
  have h4 : Entails.eval a c1376 := derived1376 a h
  have h5 : Entails.eval a c1406 := derived1406 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1381 := derived1381 a h
  have h9 : Entails.eval a c1407 := derived1407 a h
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c1269, some c1400, some c329, some c85, some c294, some c1273, some c363, some c360, some c292, some c311, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 57) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c132, c1269, c1400, c329, c85, c294, c1273, c363, c360, c292, c311] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c1269 := derived1269 a h
  have h2 : Entails.eval a c1400 := derived1400 a h
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c1273 := derived1273 a h
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c360 := h 359 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1408, some c1401, some c1269, some c1402, some c132, some c140, some c937, some c1409, some c53, some c55, some c330, some c302, some c288, some c93, some c26, some c86, some c385, some c1278, some c316, some c97, some c28, some c68, some c124, some c366, some c1355, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 57) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c1408, c1401, c1269, c1402, c132, c140, c937, c1409, c53, c55, c330, c302, c288, c93, c26, c86, c385, c1278, c316, c97, c28, c68, c124, c366, c1355] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c1408 := derived1408 a h
  have h1 : Entails.eval a c1401 := derived1401 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c1402 := derived1402 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c937 := derived937 a h
  have h7 : Entails.eval a c1409 := derived1409 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c288 := h 287 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c1278 := derived1278 a h
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c97 := h 96 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c68 := h 67 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c366 := h 365 (by decide)
  have h24 : Entails.eval a c1355 := derived1355 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1408, some c1401, some c1269, some c1397, some c1410, some c1265, some c158, some c937, some c1402, some c1390, some c1405, some c124, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 57) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c1408, c1401, c1269, c1397, c1410, c1265, c158, c937, c1402, c1390, c1405, c124] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c1408 := derived1408 a h
  have h1 : Entails.eval a c1401 := derived1401 a h
  have h2 : Entails.eval a c1269 := derived1269 a h
  have h3 : Entails.eval a c1397 := derived1397 a h
  have h4 : Entails.eval a c1410 := derived1410 a h
  have h5 : Entails.eval a c1265 := derived1265 a h
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c937 := derived937 a h
  have h8 : Entails.eval a c1402 := derived1402 a h
  have h9 : Entails.eval a c1390 := derived1390 a h
  have h10 : Entails.eval a c1405 := derived1405 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨33, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1408, some c1397, some c1401, some c1269, some c1410, some c1265, some c158, some c1411, some c53, some c55, some c331, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 57) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1408, c1397, c1401, c1269, c1410, c1265, c158, c1411, c53, c55, c331] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1408 := derived1408 a h
  have h1 : Entails.eval a c1397 := derived1397 a h
  have h2 : Entails.eval a c1401 := derived1401 a h
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c1410 := derived1410 a h
  have h5 : Entails.eval a c1265 := derived1265 a h
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c1411 := derived1411 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨20, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1278, some c39, some c54, some c282, some c333, some c223, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 57) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c1278, c39, c54, c282, c333, c223] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c1278 := derived1278 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c942, some c659, some c871, some c72, some c95, some c365, some c343, some c80, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 57) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c942, c659, c871, c72, c95, c365, c343, c80] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c942 := derived942 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c871 := derived871 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1412, some c1268, some c1267, some c24, some c32, some c41, some c1029, some c1278, some c1269, some c1372, some c1263, some c158, some c332, some c309, some c328, some c55, some c1413, some c5, some c189, some c177, some c1414, some c124, some c43, some c731, some c232, some c282, some c224, some c49, some c127, some c334, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 57) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c1412, c1268, c1267, c24, c32, c41, c1029, c1278, c1269, c1372, c1263, c158, c332, c309, c328, c55, c1413, c5, c189, c177, c1414, c124, c43, c731, c232, c282, c224, c49, c127, c334] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1268 := derived1268 a h
  have h2 : Entails.eval a c1267 := derived1267 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c1029 := derived1029 a h
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c1269 := derived1269 a h
  have h9 : Entails.eval a c1372 := derived1372 a h
  have h10 : Entails.eval a c1263 := derived1263 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c55 := h 54 (by decide)
  have h16 : Entails.eval a c1413 := derived1413 a h
  have h17 : Entails.eval a c5 := h 4 (by decide)
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c1414 := derived1414 a h
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c43 := h 42 (by decide)
  have h23 : Entails.eval a c731 := derived731 a h
  have h24 : Entails.eval a c232 := h 231 (by decide)
  have h25 : Entails.eval a c282 := h 281 (by decide)
  have h26 : Entails.eval a c224 := h 223 (by decide)
  have h27 : Entails.eval a c49 := h 48 (by decide)
  have h28 : Entails.eval a c127 := h 126 (by decide)
  have h29 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1269, some c1415, some c1266, some c24, some c329, some c328, some c294, some c234, some c690, some c23, some c117, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 57) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1269, c1415, c1266, c24, c329, c328, c294, c234, c690, c23, c117] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1269 := derived1269 a h
  have h1 : Entails.eval a c1415 := derived1415 a h
  have h2 : Entails.eval a c1266 := derived1266 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c234 := h 233 (by decide)
  have h8 : Entails.eval a c690 := derived690 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c32, some c24, some c1262, some c667, some c1416, some c217, some c1174, some c302, some c86, some c184, some c318, some c871, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 57) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c1415, c1266, c32, c24, c1262, c667, c1416, c217, c1174, c302, c86, c184, c318, c871] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c1262 := derived1262 a h
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c1416 := derived1416 a h
  have h7 : Entails.eval a c217 := h 216 (by decide)
  have h8 : Entails.eval a c1174 := derived1174 a h
  have h9 : Entails.eval a c302 := h 301 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c871 := derived871 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c26, some c302, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 57) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c18, c26, c302] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c24, some c32, some c1418, some c1278, some c1397, some c1264, some c1417, some c149, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 57) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1415, c1266, c24, c32, c1418, c1278, c1397, c1264, c1417, c149] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1278 := derived1278 a h
  have h6 : Entails.eval a c1397 := derived1397 a h
  have h7 : Entails.eval a c1264 := derived1264 a h
  have h8 : Entails.eval a c1417 := derived1417 a h
  have h9 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c32, some c24, some c329, some c328, some c298, some c1416, some c171, some c158, some c133, some c364, some c3, some c214, some c212, some c712, some c23, some c1108, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 57) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c1415, c1266, c32, c24, c329, c328, c298, c1416, c171, c158, c133, c364, c3, c214, c212, c712, c23, c1108] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c298 := h 297 (by decide)
  have h7 : Entails.eval a c1416 := derived1416 a h
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c364 := h 363 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c214 := h 213 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c712 := derived712 a h
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c1108 := derived1108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c32, some c1418, some c39, some c236, some c67, some c79, some c264, some c342, some c86, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 57) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c24, c32, c1418, c39, c236, c67, c79, c264, c342, c86] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c342 := h 341 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1419, some c1420, some c1415, some c1266, some c1397, some c32, some c24, some c1269, some c158, some c332, some c309, some c46, some c1421, some c123, some c56, some c690, some c43, some c183, some c232, some c181, some c83, some c219, some c342, some c189, some c96, some c304, some c212, some c162, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 57) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c1419, c1420, c1415, c1266, c1397, c32, c24, c1269, c158, c332, c309, c46, c1421, c123, c56, c690, c43, c183, c232, c181, c83, c219, c342, c189, c96, c304, c212, c162] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c1419 := derived1419 a h
  have h1 : Entails.eval a c1420 := derived1420 a h
  have h2 : Entails.eval a c1415 := derived1415 a h
  have h3 : Entails.eval a c1266 := derived1266 a h
  have h4 : Entails.eval a c1397 := derived1397 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1269 := derived1269 a h
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c332 := h 331 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c1421 := derived1421 a h
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c690 := derived690 a h
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c181 := h 180 (by decide)
  have h20 : Entails.eval a c83 := h 82 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  have h22 : Entails.eval a c342 := h 341 (by decide)
  have h23 : Entails.eval a c189 := h 188 (by decide)
  have h24 : Entails.eval a c96 := h 95 (by decide)
  have h25 : Entails.eval a c304 := h 303 (by decide)
  have h26 : Entails.eval a c212 := h 211 (by decide)
  have h27 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c32, some c1418, some c39, some c1421, some c46, some c66, some c318, some c264, some c111, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 57) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c24, c32, c1418, c39, c1421, c46, c66, c318, c264, c111] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c1418 := derived1418 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1421 := derived1421 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c24, some c32, some c1418, some c1058, some c364, some c1270, some c72, some c66, some c318, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 57) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1415, c1266, c24, c32, c1418, c1058, c364, c1270, c72, c66, c318] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c1270 := derived1270 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c32, some c24, some c1397, some c1418, some c1278, some c1419, some c1420, some c1422, some c683, some c222, some c1423, some c123, some c690, some c712, some c310, some c1424, some c158, some c183, some c332, some c309, some c212, some c1311, some c56, some c193, some c250, some c306, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 57) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c1415, c1266, c32, c24, c1397, c1418, c1278, c1419, c1420, c1422, c683, c222, c1423, c123, c690, c712, c310, c1424, c158, c183, c332, c309, c212, c1311, c56, c193, c250, c306] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c1397 := derived1397 a h
  have h5 : Entails.eval a c1418 := derived1418 a h
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c1419 := derived1419 a h
  have h8 : Entails.eval a c1420 := derived1420 a h
  have h9 : Entails.eval a c1422 := derived1422 a h
  have h10 : Entails.eval a c683 := derived683 a h
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c1423 := derived1423 a h
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c690 := derived690 a h
  have h15 : Entails.eval a c712 := derived712 a h
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c1424 := derived1424 a h
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c332 := h 331 (by decide)
  have h21 : Entails.eval a c309 := h 308 (by decide)
  have h22 : Entails.eval a c212 := h 211 (by decide)
  have h23 : Entails.eval a c1311 := derived1311 a h
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c193 := h 192 (by decide)
  have h26 : Entails.eval a c250 := h 249 (by decide)
  have h27 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c1425, some c1267, some c41, some c364, some c1271, some c81, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 57) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1415, c1266, c1425, c1267, c41, c364, c1271, c81] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c1425 := derived1425 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c1271 := derived1271 a h
  have h7 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c24, some c51, some c71, some c310, some c809, some c31, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 57) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c32, c24, c51, c71, c310, c809, c31] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c809 := derived809 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c1425, some c1267, some c41, some c39, some c282, some c43, some c117, some c1427, some c365, some c81, some c79, some c240, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 57) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c1415, c1266, c1425, c1267, c41, c39, c282, c43, c117, c1427, c365, c81, c79, c240] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c1425 := derived1425 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c1427 := derived1427 a h
  have h10 : Entails.eval a c365 := h 364 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1426, some c1425, some c1415, some c1266, some c24, some c32, some c1267, some c41, some c1278, some c1372, some c1263, some c1428, some c5, some c177, some c158, some c309, some c189, some c942, some c659, some c72, some c365, some c51, some c80, some c310, some c343, some c100, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 57) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c1426, c1425, c1415, c1266, c24, c32, c1267, c41, c1278, c1372, c1263, c1428, c5, c177, c158, c309, c189, c942, c659, c72, c365, c51, c80, c310, c343, c100] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c1426 := derived1426 a h
  have h1 : Entails.eval a c1425 := derived1425 a h
  have h2 : Entails.eval a c1415 := derived1415 a h
  have h3 : Entails.eval a c1266 := derived1266 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c1267 := derived1267 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c1278 := derived1278 a h
  have h9 : Entails.eval a c1372 := derived1372 a h
  have h10 : Entails.eval a c1263 := derived1263 a h
  have h11 : Entails.eval a c1428 := derived1428 a h
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c942 := derived942 a h
  have h18 : Entails.eval a c659 := derived659 a h
  have h19 : Entails.eval a c72 := h 71 (by decide)
  have h20 : Entails.eval a c365 := h 364 (by decide)
  have h21 : Entails.eval a c51 := h 50 (by decide)
  have h22 : Entails.eval a c80 := h 79 (by decide)
  have h23 : Entails.eval a c310 := h 309 (by decide)
  have h24 : Entails.eval a c343 := h 342 (by decide)
  have h25 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1415, some c1266, some c24, some c32, some c1425, some c1267, some c41, some c1278, some c1372, some c1263, some c1426, some c158, some c332, some c1155, some c1428, some c5, some c1429, some c117, some c43, some c731, some c232, some c282, some c224, some c49, some c127, some c334, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 57) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c1415, c1266, c24, c32, c1425, c1267, c41, c1278, c1372, c1263, c1426, c158, c332, c1155, c1428, c5, c1429, c117, c43, c731, c232, c282, c224, c49, c127, c334] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c1415 := derived1415 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c1425 := derived1425 a h
  have h5 : Entails.eval a c1267 := derived1267 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c1372 := derived1372 a h
  have h9 : Entails.eval a c1263 := derived1263 a h
  have h10 : Entails.eval a c1426 := derived1426 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c1155 := derived1155 a h
  have h14 : Entails.eval a c1428 := derived1428 a h
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c1429 := derived1429 a h
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c731 := derived731 a h
  have h20 : Entails.eval a c232 := h 231 (by decide)
  have h21 : Entails.eval a c282 := h 281 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c49 := h 48 (by decide)
  have h24 : Entails.eval a c127 := h 126 (by decide)
  have h25 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨40, by decide⟩, true), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c72, some c659, some c81, some c79, some c369, some c343, some c83, some c27, some c117, some c40, some c71, some c242, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 57) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c28, c72, c659, c81, c79, c369, c343, c83, c27, c117, c40, c71, c242] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨30, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1267, some c1279, some c158, some c1272, some c81, some c1271, some c20, some c28, some c347, some c1370, some c1431, some c5, some c134, some c126, some c300, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 57) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c1267, c1279, c158, c1272, c81, c1271, c20, c28, c347, c1370, c1431, c5, c134, c126, c300] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c1267 := derived1267 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c1271 := derived1271 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c1370 := derived1370 a h
  have h10 : Entails.eval a c1431 := derived1431 a h
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1279, some c1277, some c1262, some c1263, some c141, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 57) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1279, c1277, c1262, c1263, c141] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1279 := derived1279 a h
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1262 := derived1262 a h
  have h3 : Entails.eval a c1263 := derived1263 a h
  have h4 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1267, some c1430, some c1279, some c1277, some c1433, some c1432, some c1155, some c52, some c61, some c364, some c365, some c331, some c183, some c220, some c621, some c71, some c1323, some c659, some c700, some c327, some c871, some c1321, some c133, some c170, some c1, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 57) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c1267, c1430, c1279, c1277, c1433, c1432, c1155, c52, c61, c364, c365, c331, c183, c220, c621, c71, c1323, c659, c700, c327, c871, c1321, c133, c170, c1] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c1267 := derived1267 a h
  have h1 : Entails.eval a c1430 := derived1430 a h
  have h2 : Entails.eval a c1279 := derived1279 a h
  have h3 : Entails.eval a c1277 := derived1277 a h
  have h4 : Entails.eval a c1433 := derived1433 a h
  have h5 : Entails.eval a c1432 := derived1432 a h
  have h6 : Entails.eval a c1155 := derived1155 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c364 := h 363 (by decide)
  have h10 : Entails.eval a c365 := h 364 (by decide)
  have h11 : Entails.eval a c331 := h 330 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c621 := derived621 a h
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c1323 := derived1323 a h
  have h17 : Entails.eval a c659 := derived659 a h
  have h18 : Entails.eval a c700 := derived700 a h
  have h19 : Entails.eval a c327 := h 326 (by decide)
  have h20 : Entails.eval a c871 := derived871 a h
  have h21 : Entails.eval a c1321 := derived1321 a h
  have h22 : Entails.eval a c133 := h 132 (by decide)
  have h23 : Entails.eval a c170 := h 169 (by decide)
  have h24 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1277, some c25, some c871, some c17, some c1381, some c1284, some c297, some c848, some c337, some c383, some c51, some c159, some c14, some c193, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 57) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c1430, c1277, c25, c871, c17, c1381, c1284, c297, c848, c337, c383, c51, c159, c14, c193] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c871 := derived871 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1381 := derived1381 a h
  have h6 : Entails.eval a c1284 := derived1284 a h
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c848 := derived848 a h
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨26, by decide⟩, false), (⟨42, by decide⟩, false), (⟨56, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1277, some c17, some c25, some c1029, some c329, some c101, some c300, some c386, some c387, some c60, some c99, some c1284, some c124, some c848, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 57) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c1277, c17, c25, c1029, c329, c101, c300, c386, c387, c60, c99, c1284, c124, c848] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c1277 := derived1277 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c1029 := derived1029 a h
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c386 := h 385 (by decide)
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c1284 := derived1284 a h
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c848 := derived848 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1279, some c1277, some c1267, some c1434, some c25, some c871, some c659, some c1276, some c1435, some c1263, some c134, some c126, some c1436, some c52, some c364, some c365, some c362, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 57) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1430, c1279, c1277, c1267, c1434, c25, c871, c659, c1276, c1435, c1263, c134, c126, c1436, c52, c364, c365, c362] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c1434 := derived1434 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c871 := derived871 a h
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c1276 := derived1276 a h
  have h9 : Entails.eval a c1435 := derived1435 a h
  have h10 : Entails.eval a c1263 := derived1263 a h
  have h11 : Entails.eval a c134 := h 133 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c1436 := derived1436 a h
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c364 := h 363 (by decide)
  have h16 : Entails.eval a c365 := h 364 (by decide)
  have h17 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1279, some c1277, some c1437, some c33, some c26, some c18, some c1155, some c302, some c158, some c92, some c1309, some c659, some c1276, some c318, some c66, some c109, some c367, some c341, some c117, some c843, some c358, some c103, some c108, some c390, some c397, some c376, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 57) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c1430, c1279, c1277, c1437, c33, c26, c18, c1155, c302, c158, c92, c1309, c659, c1276, c318, c66, c109, c367, c341, c117, c843, c358, c103, c108, c390, c397, c376] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1437 := derived1437 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c1155 := derived1155 a h
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c1309 := derived1309 a h
  have h12 : Entails.eval a c659 := derived659 a h
  have h13 : Entails.eval a c1276 := derived1276 a h
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c367 := h 366 (by decide)
  have h18 : Entails.eval a c341 := h 340 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c843 := derived843 a h
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  have h23 : Entails.eval a c108 := h 107 (by decide)
  have h24 : Entails.eval a c390 := h 389 (by decide)
  have h25 : Entails.eval a c397 := h 396 (by decide)
  have h26 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1279, some c1277, some c1437, some c33, some c26, some c1438, some c52, some c364, some c365, some c183, some c621, some c71, some c77, some c659, some c342, some c92, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 57) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1430, c1279, c1277, c1437, c33, c26, c1438, c52, c364, c365, c183, c621, c71, c77, c659, c342, c92] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1437 := derived1437 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c1438 := derived1438 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c621 := derived621 a h
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c659 := derived659 a h
  have h15 : Entails.eval a c342 := h 341 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1279, some c1277, some c1437, some c18, some c26, some c33, some c1439, some c1262, some c683, some c141, some c92, some c217, some c216, some c1280, some c300, some c168, some c156, some c318, some c340, some c66, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 57) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c1430, c1279, c1277, c1437, c18, c26, c33, c1439, c1262, c683, c141, c92, c217, c216, c1280, c300, c168, c156, c318, c340, c66] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  have h3 : Entails.eval a c1437 := derived1437 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c1439 := derived1439 a h
  have h8 : Entails.eval a c1262 := derived1262 a h
  have h9 : Entails.eval a c683 := derived683 a h
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c1280 := derived1280 a h
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c156 := h 155 (by decide)
  have h18 : Entails.eval a c318 := h 317 (by decide)
  have h19 : Entails.eval a c340 := h 339 (by decide)
  have h20 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1430, some c1277, some c1279, some c1440, some c1268, some c1266, some c33, some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 57) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1430, c1277, c1279, c1440, c1268, c1266, c33] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1430 := derived1430 a h
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1279 := derived1279 a h
  have h3 : Entails.eval a c1440 := derived1440 a h
  have h4 : Entails.eval a c1268 := derived1268 a h
  have h5 : Entails.eval a c1266 := derived1266 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1442 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1319, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 57) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c1441, c1319] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1319 := derived1319 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1443 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1336, some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 57) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c1441, c1336] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1336 := derived1336 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1444 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1375, some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 57) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c1441, c1375] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1375 := derived1375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1445 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, true), (⟨48, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c80, some c100, some c350, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 57) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1444, c80, c100, c350] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1442, some c1444, some c1441, some c1443, some c1267, some c101, some c28, some c1278, some c1372, some c95, some c1014, some c328, some c1349, some c153, some c366, some c81, some c1445, some c117, some c3, some c731, some c672, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 57) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c1442, c1444, c1441, c1443, c1267, c101, c28, c1278, c1372, c95, c1014, c328, c1349, c153, c366, c81, c1445, c117, c3, c731, c672] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c1442 := derived1442 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1443 := derived1443 a h
  have h4 : Entails.eval a c1267 := derived1267 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c1372 := derived1372 a h
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c1014 := derived1014 a h
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c1349 := derived1349 a h
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c1445 := derived1445 a h
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c3 := h 2 (by decide)
  have h19 : Entails.eval a c731 := derived731 a h
  have h20 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1442, some c1444, some c1443, some c1267, some c101, some c28, some c1278, some c1372, some c1263, some c95, some c1446, some c158, some c1271, some c81, some c48, some c1445, some c117, some c1089, some c43, some c731, some c700, some c282, some c672, some c224, some c454, some c330, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 57) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1442, c1444, c1443, c1267, c101, c28, c1278, c1372, c1263, c95, c1446, c158, c1271, c81, c48, c1445, c117, c1089, c43, c731, c700, c282, c672, c224, c454, c330] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1442 := derived1442 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1443 := derived1443 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c1372 := derived1372 a h
  have h8 : Entails.eval a c1263 := derived1263 a h
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c1446 := derived1446 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c1271 := derived1271 a h
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c48 := h 47 (by decide)
  have h15 : Entails.eval a c1445 := derived1445 a h
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c1089 := derived1089 a h
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c731 := derived731 a h
  have h20 : Entails.eval a c700 := derived700 a h
  have h21 : Entails.eval a c282 := h 281 (by decide)
  have h22 : Entails.eval a c672 := derived672 a h
  have h23 : Entails.eval a c224 := h 223 (by decide)
  have h24 : Entails.eval a c454 := derived454 a h
  have h25 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c1442, some c1443, some c1267, some c101, some c28, some c1278, some c1372, some c1263, some c95, some c133, some c248, some c1155, some c302, some c388, some c220, some c651, some c329, some c81, some c171, some c1445, some c3, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 57) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c1444, c1442, c1443, c1267, c101, c28, c1278, c1372, c1263, c95, c133, c248, c1155, c302, c388, c220, c651, c329, c81, c171, c1445, c3] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c1442 := derived1442 a h
  have h2 : Entails.eval a c1443 := derived1443 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1278 := derived1278 a h
  have h7 : Entails.eval a c1372 := derived1372 a h
  have h8 : Entails.eval a c1263 := derived1263 a h
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c1155 := derived1155 a h
  have h13 : Entails.eval a c302 := h 301 (by decide)
  have h14 : Entails.eval a c388 := h 387 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c651 := derived651 a h
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c171 := h 170 (by decide)
  have h20 : Entails.eval a c1445 := derived1445 a h
  have h21 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1448, some c1277, some c1447, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 57) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1448, c1277, c1447] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1448 := derived1448 a h
  have h1 : Entails.eval a c1277 := derived1277 a h
  have h2 : Entails.eval a c1447 := derived1447 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1442, some c1444, some c1441, some c1443, some c1449, some c32, some c1418, some c1278, some c250, some c1423, some c1397, some c123, some c43, some c276, some c255, some c310, some c23, some c672, some c136, some c9, some c153, some c173, some c674, some c328, some c1360, some c294, some c1339, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 57) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c1442, c1444, c1441, c1443, c1449, c32, c1418, c1278, c250, c1423, c1397, c123, c43, c276, c255, c310, c23, c672, c136, c9, c153, c173, c674, c328, c1360, c294, c1339] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c1442 := derived1442 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1443 := derived1443 a h
  have h4 : Entails.eval a c1449 := derived1449 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c1418 := derived1418 a h
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c1423 := derived1423 a h
  have h10 : Entails.eval a c1397 := derived1397 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  have h16 : Entails.eval a c23 := h 22 (by decide)
  have h17 : Entails.eval a c672 := derived672 a h
  have h18 : Entails.eval a c136 := h 135 (by decide)
  have h19 : Entails.eval a c9 := h 8 (by decide)
  have h20 : Entails.eval a c153 := h 152 (by decide)
  have h21 : Entails.eval a c173 := h 172 (by decide)
  have h22 : Entails.eval a c674 := derived674 a h
  have h23 : Entails.eval a c328 := h 327 (by decide)
  have h24 : Entails.eval a c1360 := derived1360 a h
  have h25 : Entails.eval a c294 := h 293 (by decide)
  have h26 : Entails.eval a c1339 := derived1339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1444, some c1443, some c1442, some c1441, some c1449, some c32, some c1397, some c1423, some c1418, some c123, some c1278, some c43, some c250, some c276, some c672, some c255, some c310, some c23, some c1450, some c3, some c45, some c1194, some c911, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 57) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c1444, c1443, c1442, c1441, c1449, c32, c1397, c1423, c1418, c123, c1278, c43, c250, c276, c672, c255, c310, c23, c1450, c3, c45, c1194, c911] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c1444 := derived1444 a h
  have h1 : Entails.eval a c1443 := derived1443 a h
  have h2 : Entails.eval a c1442 := derived1442 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1449 := derived1449 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c1397 := derived1397 a h
  have h7 : Entails.eval a c1423 := derived1423 a h
  have h8 : Entails.eval a c1418 := derived1418 a h
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c1278 := derived1278 a h
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c672 := derived672 a h
  have h15 : Entails.eval a c255 := h 254 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c1450 := derived1450 a h
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c1194 := derived1194 a h
  have h22 : Entails.eval a c911 := derived911 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1442, some c1443, some c1444, some c1449, some c1451, some c1277, some c1279, some c25, some c133, some c1155, some c18, some c1418, some c1262, some c158, some c92, some c1309, some c659, some c318, some c109, some c117, some c36, some c103, some c760, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 57) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1442, c1443, c1444, c1449, c1451, c1277, c1279, c25, c133, c1155, c18, c1418, c1262, c158, c92, c1309, c659, c318, c109, c117, c36, c103, c760] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1442 := derived1442 a h
  have h1 : Entails.eval a c1443 := derived1443 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c1449 := derived1449 a h
  have h4 : Entails.eval a c1451 := derived1451 a h
  have h5 : Entails.eval a c1277 := derived1277 a h
  have h6 : Entails.eval a c1279 := derived1279 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c1155 := derived1155 a h
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c1418 := derived1418 a h
  have h12 : Entails.eval a c1262 := derived1262 a h
  have h13 : Entails.eval a c158 := h 157 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c1309 := derived1309 a h
  have h16 : Entails.eval a c659 := derived659 a h
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c103 := h 102 (by decide)
  have h22 : Entails.eval a c760 := derived760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1268, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 57) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c1452, c1268] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1268 := derived1268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1454 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1266, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 57) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c1452, c1266] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1455 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1441, some c1328, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 57) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c1452, c1441, c1328] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1452, some c1441, some c1329, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 57) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c1452, c1441, c1329] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c1452 := derived1452 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1329 := derived1329 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c1441, some c45, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 57) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c1454, c1441, c45] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c1442, some c25, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 57) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c1454, c1442, c25] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c1442 := derived1442 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c1453, some c1443, some c937, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 57) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c1454, c1453, c1443, c937] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c1443 := derived1443 a h
  have h3 : Entails.eval a c937 := derived937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c1453, some c1441, some c73, some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 57) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c1454, c1453, c1441, c73] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1455, some c1456, some c123, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 57) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1455, c1456, c123] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1455 := derived1455 a h
  have h1 : Entails.eval a c1456 := derived1456 a h
  have h2 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1457, some c1443, some c329, some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 57) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c1457, c1443, c329] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c1457 := derived1457 a h
  have h1 : Entails.eval a c1443 := derived1443 a h
  have h2 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1458, some c1277, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 57) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1458, c1277] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1458 := derived1458 a h
  have h1 : Entails.eval a c1277 := derived1277 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1464 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1463, some c1452, some c1453, some c1456, some c1380, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 57) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c1463, c1452, c1453, c1456, c1380] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c1463 := derived1463 a h
  have h1 : Entails.eval a c1452 := derived1452 a h
  have h2 : Entails.eval a c1453 := derived1453 a h
  have h3 : Entails.eval a c1456 := derived1456 a h
  have h4 : Entails.eval a c1380 := derived1380 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1464, some c1459, some c158, some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p1465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 57) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c1464, c1459, c158] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c1464 := derived1464 a h
  have h1 : Entails.eval a c1459 := derived1459 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1464, some c1462, some c1459, some c171, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 57) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c1464, c1462, c1459, c171] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c1464 := derived1464 a h
  have h1 : Entails.eval a c1462 := derived1462 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1465, some c1460, some c1270, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 57) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1465, c1460, c1270] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1465 := derived1465 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1270 := derived1270 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1465, some c1453, some c1460, some c1443, some c1339, some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 57) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c1465, c1453, c1460, c1443, c1339] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c1465 := derived1465 a h
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c1460 := derived1460 a h
  have h3 : Entails.eval a c1443 := derived1443 a h
  have h4 : Entails.eval a c1339 := derived1339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1466, some c1463, some c1468, some c1253, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 57) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c1466, c1463, c1468, c1253] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c1466 := derived1466 a h
  have h1 : Entails.eval a c1463 := derived1463 a h
  have h2 : Entails.eval a c1468 := derived1468 a h
  have h3 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1467, some c1453, some c1461, some c36, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 57) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1467, c1453, c1461, c36] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1467 := derived1467 a h
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c1461 := derived1461 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1469, some c1453, some c1467, some c37, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 57) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1469, c1453, c1467, c37] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1469 := derived1469 a h
  have h1 : Entails.eval a c1453 := derived1453 a h
  have h2 : Entails.eval a c1467 := derived1467 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1471, some c1470, some c1458, some c276]
def p1472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 57) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1471, c1470, c1458, c276] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1471 := derived1471 a h
  have h1 : Entails.eval a c1470 := derived1470 a h
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1472

end CochromaticTwenty.Certificates.B16_3_2
