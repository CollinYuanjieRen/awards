import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Steps0400_0499

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1403 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1398, some c1385, some c37, some c1400, some c1402, some c831, some c199, some c38, some c196, some c212, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1403 : lratChecker f1403 p1403 = .success := by decide +kernel
theorem unsat1403 : Unsatisfiable (PosFin 31) f1403 := by
  apply lratCheckerSound f1403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1403
  · intro a ha; simp [p1403] at ha; subst a; trivial
  · exact checked1403
theorem derived1403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1403 := by
  apply localUnsat_implies_entails f1403 [c1328, c1246, c1398, c1385, c37, c1400, c1402, c831, c199, c38, c196, c212] c1403 unsat1403 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1398 := derived1398 a h
  have h3 : Entails.eval a c1385 := derived1385 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1400 := derived1400 a h
  have h6 : Entails.eval a c1402 := derived1402 a h
  have h7 : Entails.eval a c831 := h 830 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1404 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1403, some c1398, some c1332, some c1336, some c1375, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1404 : lratChecker f1404 p1404 = .success := by decide +kernel
theorem unsat1404 : Unsatisfiable (PosFin 31) f1404 := by
  apply lratCheckerSound f1404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1404
  · intro a ha; simp [p1404] at ha; subst a; trivial
  · exact checked1404
theorem derived1404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1404 := by
  apply localUnsat_implies_entails f1404 [c1403, c1398, c1332, c1336, c1375] c1404 unsat1404 (by rfl) a
  have h0 : Entails.eval a c1403 := derived1403 a h
  have h1 : Entails.eval a c1398 := derived1398 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1336 := derived1336 a h
  have h4 : Entails.eval a c1375 := derived1375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1405 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1385, some c37, some c1403, some c1404, some c498, some c54, some c307, some c19, some c682, some c197, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1405 : lratChecker f1405 p1405 = .success := by decide +kernel
theorem unsat1405 : Unsatisfiable (PosFin 31) f1405 := by
  apply lratCheckerSound f1405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1405
  · intro a ha; simp [p1405] at ha; subst a; trivial
  · exact checked1405
theorem derived1405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1405 := by
  apply localUnsat_implies_entails f1405 [c1246, c1385, c37, c1403, c1404, c498, c54, c307, c19, c682, c197] c1405 unsat1405 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1385 := derived1385 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c1403 := derived1403 a h
  have h4 : Entails.eval a c1404 := derived1404 a h
  have h5 : Entails.eval a c498 := h 497 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c682 := h 681 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1406 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1398, some c1405, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1406 : lratChecker f1406 p1406 = .success := by decide +kernel
theorem unsat1406 : Unsatisfiable (PosFin 31) f1406 := by
  apply lratCheckerSound f1406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1406
  · intro a ha; simp [p1406] at ha; subst a; trivial
  · exact checked1406
theorem derived1406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1406 := by
  apply localUnsat_implies_entails f1406 [c1398, c1405] c1406 unsat1406 (by rfl) a
  have h0 : Entails.eval a c1398 := derived1398 a h
  have h1 : Entails.eval a c1405 := derived1405 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1407 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1406, some c1387, some c770, some c681, some c852, some c54, some c197, some c767, some c198, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1407 : lratChecker f1407 p1407 = .success := by decide +kernel
theorem unsat1407 : Unsatisfiable (PosFin 31) f1407 := by
  apply lratCheckerSound f1407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1407
  · intro a ha; simp [p1407] at ha; subst a; trivial
  · exact checked1407
theorem derived1407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1407 := by
  apply localUnsat_implies_entails f1407 [c1246, c1328, c1406, c1387, c770, c681, c852, c54, c197, c767, c198] c1407 unsat1407 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c770 := h 769 (by decide)
  have h5 : Entails.eval a c681 := h 680 (by decide)
  have h6 : Entails.eval a c852 := h 851 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c767 := h 766 (by decide)
  have h10 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1408 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1408 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c28, some c1406, some c1387, some c414, some c566, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1408 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1408 : lratChecker f1408 p1408 = .success := by decide +kernel
theorem unsat1408 : Unsatisfiable (PosFin 31) f1408 := by
  apply lratCheckerSound f1408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1408
  · intro a ha; simp [p1408] at ha; subst a; trivial
  · exact checked1408
theorem derived1408 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1408 := by
  apply localUnsat_implies_entails f1408 [c1328, c28, c1406, c1387, c414, c566] c1408 unsat1408 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c414 := h 413 (by decide)
  have h5 : Entails.eval a c566 := h 565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1409 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1409 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1406, some c1387, some c1407, some c1332, some c1336, some c28, some c337, some c1408, some c615, some c38, some c72, some c609, some c312, some c608, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1409 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1409 : lratChecker f1409 p1409 = .success := by decide +kernel
theorem unsat1409 : Unsatisfiable (PosFin 31) f1409 := by
  apply lratCheckerSound f1409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1409
  · intro a ha; simp [p1409] at ha; subst a; trivial
  · exact checked1409
theorem derived1409 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1409 := by
  apply localUnsat_implies_entails f1409 [c1328, c1246, c1406, c1387, c1407, c1332, c1336, c28, c337, c1408, c615, c38, c72, c609, c312, c608] c1409 unsat1409 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1407 := derived1407 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c337 := h 336 (by decide)
  have h9 : Entails.eval a c1408 := derived1408 a h
  have h10 : Entails.eval a c615 := h 614 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c609 := h 608 (by decide)
  have h14 : Entails.eval a c312 := h 311 (by decide)
  have h15 : Entails.eval a c608 := h 607 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1410 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1410 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1409, some c1406, some c1387, some c1332, some c1336, some c26, some c28, some c31, some c337, some c402, some c274, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1410 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1410 : lratChecker f1410 p1410 = .success := by decide +kernel
theorem unsat1410 : Unsatisfiable (PosFin 31) f1410 := by
  apply lratCheckerSound f1410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1410
  · intro a ha; simp [p1410] at ha; subst a; trivial
  · exact checked1410
theorem derived1410 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1410 := by
  apply localUnsat_implies_entails f1410 [c1246, c1409, c1406, c1387, c1332, c1336, c26, c28, c31, c337, c402, c274] c1410 unsat1410 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1409 := derived1409 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c402 := h 401 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1411 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1411 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1410, some c1409, some c1406, some c1387, some c682, some c767, some c768, some c82, some c84, some c847, some c218, some c27, some c224, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1411 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1411 : lratChecker f1411 p1411 = .success := by decide +kernel
theorem unsat1411 : Unsatisfiable (PosFin 31) f1411 := by
  apply lratCheckerSound f1411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1411
  · intro a ha; simp [p1411] at ha; subst a; trivial
  · exact checked1411
theorem derived1411 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1411 := by
  apply localUnsat_implies_entails f1411 [c1328, c1410, c1409, c1406, c1387, c682, c767, c768, c82, c84, c847, c218, c27, c224] c1411 unsat1411 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1410 := derived1410 a h
  have h2 : Entails.eval a c1409 := derived1409 a h
  have h3 : Entails.eval a c1406 := derived1406 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c682 := h 681 (by decide)
  have h6 : Entails.eval a c767 := h 766 (by decide)
  have h7 : Entails.eval a c768 := h 767 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c847 := h 846 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1412 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1412 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1406, some c1387, some c1410, some c770, some c1411, some c54, some c37, some c852, some c311, some c167, some c21, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1412 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1412 : lratChecker f1412 p1412 = .success := by decide +kernel
theorem unsat1412 : Unsatisfiable (PosFin 31) f1412 := by
  apply lratCheckerSound f1412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1412
  · intro a ha; simp [p1412] at ha; subst a; trivial
  · exact checked1412
theorem derived1412 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1412 := by
  apply localUnsat_implies_entails f1412 [c1246, c1406, c1387, c1410, c770, c1411, c54, c37, c852, c311, c167, c21] c1412 unsat1412 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1406 := derived1406 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1410 := derived1410 a h
  have h4 : Entails.eval a c770 := h 769 (by decide)
  have h5 : Entails.eval a c1411 := derived1411 a h
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c852 := h 851 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1413 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1413 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c265, some c167, some c526, some c27, some c421, some c168, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1413 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1413 : lratChecker f1413 p1413 = .success := by decide +kernel
theorem unsat1413 : Unsatisfiable (PosFin 31) f1413 := by
  apply lratCheckerSound f1413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1413
  · intro a ha; simp [p1413] at ha; subst a; trivial
  · exact checked1413
theorem derived1413 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1413 := by
  apply localUnsat_implies_entails f1413 [c1246, c1328, c265, c167, c526, c27, c421, c168] c1413 unsat1413 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c526 := h 525 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c421 := h 420 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1414 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1414 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1412, some c1406, some c1387, some c334, some c1413, some c736, some c740, some c737, some c238, some c57, some c136, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1414 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1414 : lratChecker f1414 p1414 = .success := by decide +kernel
theorem unsat1414 : Unsatisfiable (PosFin 31) f1414 := by
  apply lratCheckerSound f1414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1414
  · intro a ha; simp [p1414] at ha; subst a; trivial
  · exact checked1414
theorem derived1414 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1414 := by
  apply localUnsat_implies_entails f1414 [c1246, c1328, c1412, c1406, c1387, c334, c1413, c736, c740, c737, c238, c57, c136] c1414 unsat1414 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1406 := derived1406 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c1413 := derived1413 a h
  have h7 : Entails.eval a c736 := h 735 (by decide)
  have h8 : Entails.eval a c740 := h 739 (by decide)
  have h9 : Entails.eval a c737 := h 736 (by decide)
  have h10 : Entails.eval a c238 := h 237 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1415 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1415 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1406, some c1387, some c353, some c800, some c431, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1415 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1415 : lratChecker f1415 p1415 = .success := by decide +kernel
theorem unsat1415 : Unsatisfiable (PosFin 31) f1415 := by
  apply lratCheckerSound f1415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1415
  · intro a ha; simp [p1415] at ha; subst a; trivial
  · exact checked1415
theorem derived1415 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1415 := by
  apply localUnsat_implies_entails f1415 [c1246, c1406, c1387, c353, c800, c431] c1415 unsat1415 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1406 := derived1406 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c800 := h 799 (by decide)
  have h5 : Entails.eval a c431 := h 430 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1416 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1416 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1412, some c37, some c1414, some c1415, some c311, some c38, some c485, some c301, some c439, some c627, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1416 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1416 : lratChecker f1416 p1416 = .success := by decide +kernel
theorem unsat1416 : Unsatisfiable (PosFin 31) f1416 := by
  apply lratCheckerSound f1416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1416
  · intro a ha; simp [p1416] at ha; subst a; trivial
  · exact checked1416
theorem derived1416 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1416 := by
  apply localUnsat_implies_entails f1416 [c1246, c1412, c37, c1414, c1415, c311, c38, c485, c301, c439, c627] c1416 unsat1416 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1412 := derived1412 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c1415 := derived1415 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c485 := h 484 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c439 := h 438 (by decide)
  have h10 : Entails.eval a c627 := h 626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1417 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1387, some c1406, some c1416, some c1412, some c832, some c873, some c38, some c521, some c18, some c485, some c427, some c430, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1417 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 31) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c1246, c1387, c1406, c1416, c1412, c832, c873, c38, c521, c18, c485, c427, c430] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1416 := derived1416 a h
  have h4 : Entails.eval a c1412 := derived1412 a h
  have h5 : Entails.eval a c832 := h 831 (by decide)
  have h6 : Entails.eval a c873 := h 872 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c521 := h 520 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c485 := h 484 (by decide)
  have h11 : Entails.eval a c427 := h 426 (by decide)
  have h12 : Entails.eval a c430 := h 429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1416, some c1412, some c1406, some c1387, some c832, some c1417, some c54, some c790, some c1345, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1418 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 31) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c1416, c1412, c1406, c1387, c832, c1417, c54, c790, c1345] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c1416 := derived1416 a h
  have h1 : Entails.eval a c1412 := derived1412 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c832 := h 831 (by decide)
  have h5 : Entails.eval a c1417 := derived1417 a h
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c790 := h 789 (by decide)
  have h8 : Entails.eval a c1345 := derived1345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1412, some c1406, some c1387, some c1416, some c1418, some c334, some c1414, some c1413, some c34, some c736, some c60, some c522, some c46, some c85, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1419 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 31) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1246, c1328, c1412, c1406, c1387, c1416, c1418, c334, c1414, c1413, c34, c736, c60, c522, c46, c85] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1406 := derived1406 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c1416 := derived1416 a h
  have h6 : Entails.eval a c1418 := derived1418 a h
  have h7 : Entails.eval a c334 := h 333 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1413 := derived1413 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c736 := h 735 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c522 := h 521 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1419, some c1332, some c1412, some c1406, some c1408, some c54, some c1342, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1420 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 31) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c1419, c1332, c1412, c1406, c1408, c54, c1342] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c1419 := derived1419 a h
  have h1 : Entails.eval a c1332 := derived1332 a h
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1406 := derived1406 a h
  have h4 : Entails.eval a c1408 := derived1408 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c1342 := derived1342 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1419, some c1412, some c1406, some c1387, some c337, some c802, some c431, some c536, some c80, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1421 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 31) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c1246, c1419, c1412, c1406, c1387, c337, c802, c431, c536, c80] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1419 := derived1419 a h
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1406 := derived1406 a h
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c802 := h 801 (by decide)
  have h7 : Entails.eval a c431 := h 430 (by decide)
  have h8 : Entails.eval a c536 := h 535 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1421, some c1420, some c1419, some c1332, some c1387, some c391, some c426, some c393, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1422 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 31) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c1246, c1421, c1420, c1419, c1332, c1387, c391, c426, c393] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1421 := derived1421 a h
  have h2 : Entails.eval a c1420 := derived1420 a h
  have h3 : Entails.eval a c1419 := derived1419 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1387 := derived1387 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c426 := h 425 (by decide)
  have h8 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1421, some c1420, some c1419, some c1412, some c1406, some c1387, some c80, some c592, some c278, some c328, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 31) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c1421, c1420, c1419, c1412, c1406, c1387, c80, c592, c278, c328] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c1421 := derived1421 a h
  have h1 : Entails.eval a c1420 := derived1420 a h
  have h2 : Entails.eval a c1419 := derived1419 a h
  have h3 : Entails.eval a c1412 := derived1412 a h
  have h4 : Entails.eval a c1406 := derived1406 a h
  have h5 : Entails.eval a c1387 := derived1387 a h
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c592 := h 591 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1406, some c1387, some c1419, some c1332, some c1421, some c1420, some c38, some c1423, some c85, some c57, some c775, some c391, some c393, some c1422, some c259, some c468, some c101, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1424 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 31) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1246, c1328, c1406, c1387, c1419, c1332, c1421, c1420, c38, c1423, c85, c57, c775, c391, c393, c1422, c259, c468, c101] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1419 := derived1419 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1421 := derived1421 a h
  have h7 : Entails.eval a c1420 := derived1420 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c1423 := derived1423 a h
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c775 := h 774 (by decide)
  have h13 : Entails.eval a c391 := h 390 (by decide)
  have h14 : Entails.eval a c393 := h 392 (by decide)
  have h15 : Entails.eval a c1422 := derived1422 a h
  have h16 : Entails.eval a c259 := h 258 (by decide)
  have h17 : Entails.eval a c468 := h 467 (by decide)
  have h18 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1406, some c1387, some c57, some c629, some c149, some c808, some c607, some c538, some c1332, some c135, some c584, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1425 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 31) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c1246, c1328, c1406, c1387, c57, c629, c149, c808, c607, c538, c1332, c135, c584] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c629 := h 628 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c808 := h 807 (by decide)
  have h8 : Entails.eval a c607 := h 606 (by decide)
  have h9 : Entails.eval a c538 := h 537 (by decide)
  have h10 : Entails.eval a c1332 := derived1332 a h
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c584 := h 583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1424, some c1425, some c92, some c379, some c478, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 31) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1328, c1424, c1425, c92, c379, c478] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1424 := derived1424 a h
  have h2 : Entails.eval a c1425 := derived1425 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c478 := h 477 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1387, some c1406, some c1426, some c592, some c1424, some c92, some c77, some c770, some c51, some c256, some c140, some c145, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 31) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c1328, c1387, c1406, c1426, c592, c1424, c92, c77, c770, c51, c256, c140, c145] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1426 := derived1426 a h
  have h4 : Entails.eval a c592 := h 591 (by decide)
  have h5 : Entails.eval a c1424 := derived1424 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c770 := h 769 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1428 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c592, some c1427, some c85, some c57, some c446, some c72, some c830, some c607, some c431, some c31, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 31) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c1246, c1328, c592, c1427, c85, c57, c446, c72, c830, c607, c431, c31] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c592 := h 591 (by decide)
  have h3 : Entails.eval a c1427 := derived1427 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c446 := h 445 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c830 := h 829 (by decide)
  have h9 : Entails.eval a c607 := h 606 (by decide)
  have h10 : Entails.eval a c431 := h 430 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1406, some c1387, some c1426, some c1428, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 31) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c1406, c1387, c1426, c1428] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c1406 := derived1406 a h
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c1426 := derived1426 a h
  have h3 : Entails.eval a c1428 := derived1428 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1387, some c1429, some c1406, some c566, some c57, some c431, some c72, some c54, some c640, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 31) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c1246, c1328, c1387, c1429, c1406, c566, c57, c431, c72, c54, c640] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1429 := derived1429 a h
  have h4 : Entails.eval a c1406 := derived1406 a h
  have h5 : Entails.eval a c566 := h 565 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c431 := h 430 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c640 := h 639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1429, some c1406, some c1387, some c566, some c1430, some c77, some c619, some c28, some c54, some c1332, some c352, some c429, some c282, some c487, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 31) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c1328, c1429, c1406, c1387, c566, c1430, c77, c619, c28, c54, c1332, c352, c429, c282, c487] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1429 := derived1429 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c566 := h 565 (by decide)
  have h5 : Entails.eval a c1430 := derived1430 a h
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c619 := h 618 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c1332 := derived1332 a h
  have h11 : Entails.eval a c352 := h 351 (by decide)
  have h12 : Entails.eval a c429 := h 428 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c487 := h 486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1424, some c92, some c1431, some c1429, some c1406, some c1387, some c24, some c352, some c537, some c349, some c116, some c210, some c437, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 31) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c1246, c1328, c1424, c92, c1431, c1429, c1406, c1387, c24, c352, c537, c349, c116, c210, c437] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1424 := derived1424 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c1431 := derived1431 a h
  have h5 : Entails.eval a c1429 := derived1429 a h
  have h6 : Entails.eval a c1406 := derived1406 a h
  have h7 : Entails.eval a c1387 := derived1387 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c537 := h 536 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c437 := h 436 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨21, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1424, some c92, some c1429, some c370, some c471, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 31) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1328, c1424, c92, c1429, c370, c471] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1424 := derived1424 a h
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c1429 := derived1429 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c471 := h 470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1431, some c1429, some c1424, some c1433, some c24, some c1432, some c1154, some c47, some c23, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 31) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c1328, c1431, c1429, c1424, c1433, c24, c1432, c1154, c47, c23] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1429 := derived1429 a h
  have h3 : Entails.eval a c1424 := derived1424 a h
  have h4 : Entails.eval a c1433 := derived1433 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1432 := derived1432 a h
  have h7 : Entails.eval a c1154 := derived1154 a h
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1406, some c1387, some c1434, some c57, some c85, some c1429, some c54, some c197, some c640, some c750, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 31) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c1328, c1406, c1387, c1434, c57, c85, c1429, c54, c197, c640, c750] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1406 := derived1406 a h
  have h2 : Entails.eval a c1387 := derived1387 a h
  have h3 : Entails.eval a c1434 := derived1434 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c1429 := derived1429 a h
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c640 := h 639 (by decide)
  have h10 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1429, some c1387, some c1434, some c85, some c1435, some c431, some c564, some c750, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 31) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c1246, c1328, c1429, c1387, c1434, c85, c1435, c431, c564, c750] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1429 := derived1429 a h
  have h3 : Entails.eval a c1387 := derived1387 a h
  have h4 : Entails.eval a c1434 := derived1434 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c1435 := derived1435 a h
  have h7 : Entails.eval a c431 := h 430 (by decide)
  have h8 : Entails.eval a c564 := h 563 (by decide)
  have h9 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1387, some c85, some c1429, some c564, some c750, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 31) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1328, c1387, c85, c1429, c564, c750] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1387 := derived1387 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c1429 := derived1429 a h
  have h4 : Entails.eval a c564 := h 563 (by decide)
  have h5 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1436, some c1429, some c1424, some c1406, some c1387, some c85, some c1437, some c431, some c330, some c54, some c500, some c790, some c1345, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 31) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c1246, c1328, c1436, c1429, c1424, c1406, c1387, c85, c1437, c431, c330, c54, c500, c790, c1345] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1436 := derived1436 a h
  have h3 : Entails.eval a c1429 := derived1429 a h
  have h4 : Entails.eval a c1424 := derived1424 a h
  have h5 : Entails.eval a c1406 := derived1406 a h
  have h6 : Entails.eval a c1387 := derived1387 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1437 := derived1437 a h
  have h9 : Entails.eval a c431 := h 430 (by decide)
  have h10 : Entails.eval a c330 := h 329 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c500 := h 499 (by decide)
  have h13 : Entails.eval a c790 := h 789 (by decide)
  have h14 : Entails.eval a c1345 := derived1345 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1424, some c1438, some c92, some c1436, some c1429, some c1406, some c1387, some c330, some c500, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 31) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1328, c1424, c1438, c92, c1436, c1429, c1406, c1387, c330, c500] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1424 := derived1424 a h
  have h2 : Entails.eval a c1438 := derived1438 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c1429 := derived1429 a h
  have h6 : Entails.eval a c1406 := derived1406 a h
  have h7 : Entails.eval a c1387 := derived1387 a h
  have h8 : Entails.eval a c330 := h 329 (by decide)
  have h9 : Entails.eval a c500 := h 499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 31 := directClause [(⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1406, some c1424, some c1436, some c1438, some c92, some c1433, some c1439, some c537, some c65, some c116, some c14, some c710, some c573, some c767, some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 31) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c1328, c1246, c1406, c1424, c1436, c1438, c92, c1433, c1439, c537, c65, c116, c14, c710, c573, c767] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1406 := derived1406 a h
  have h3 : Entails.eval a c1424 := derived1424 a h
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c1438 := derived1438 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c1433 := derived1433 a h
  have h8 : Entails.eval a c1439 := derived1439 a h
  have h9 : Entails.eval a c537 := h 536 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c710 := h 709 (by decide)
  have h14 : Entails.eval a c573 := h 572 (by decide)
  have h15 : Entails.eval a c767 := h 766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c963, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 31) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1440, c963] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c963 := derived963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1442 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c278, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 31) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c328, c278] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1443 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c668, some c148, some c378, some c1442, some c683, some c852, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 31) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c1441, c668, c148, c378, c1442, c683, c852] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c668 := h 667 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c1442 := derived1442 a h
  have h5 : Entails.eval a c683 := h 682 (by decide)
  have h6 : Entails.eval a c852 := h 851 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1328, some c1443, some c92, some c477, some c378, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 31) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c1441, c1328, c1443, c92, c477, c378] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1443 := derived1443 a h
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c477 := h 476 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1440, some c1441, some c1444, some c85, some c50, some c285, some c392, some c390, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 31) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1328, c1246, c1440, c1441, c1444, c85, c50, c285, c392, c390] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1444 := derived1444 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c390 := h 389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1441, some c1440, some c1444, some c1445, some c80, some c1442, some c726, some c275, some c443, some c285, some c50, some c338, some c319, some c66, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 31) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c1246, c1441, c1440, c1444, c1445, c80, c1442, c726, c275, c443, c285, c50, c338, c319, c66] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c1444 := derived1444 a h
  have h4 : Entails.eval a c1445 := derived1445 a h
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c1442 := derived1442 a h
  have h7 : Entails.eval a c726 := h 725 (by decide)
  have h8 : Entails.eval a c275 := h 274 (by decide)
  have h9 : Entails.eval a c443 := h 442 (by decide)
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c338 := h 337 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1246, some c1441, some c499, some c497, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 31) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1440, c1246, c1441, c499, c497] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c499 := h 498 (by decide)
  have h4 : Entails.eval a c497 := h 496 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1440, some c1246, some c1444, some c1446, some c1447, some c1332, some c1442, some c392, some c390, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 31) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c1441, c1440, c1246, c1444, c1446, c1447, c1332, c1442, c392, c390] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c1444 := derived1444 a h
  have h4 : Entails.eval a c1446 := derived1446 a h
  have h5 : Entails.eval a c1447 := derived1447 a h
  have h6 : Entails.eval a c1332 := derived1332 a h
  have h7 : Entails.eval a c1442 := derived1442 a h
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c390 := h 389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1440, some c1332, some c476, some c107, some c797, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 31) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1246, c1440, c1332, c476, c107, c797] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c476 := h 475 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c797 := h 796 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1246, some c1440, some c37, some c1448, some c1447, some c1332, some c1336, some c1449, some c413, some c70, some c337, some c248, some c347, some c66, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 31) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c1441, c1246, c1440, c37, c1448, c1447, c1332, c1336, c1449, c413, c70, c337, c248, c347, c66] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1448 := derived1448 a h
  have h5 : Entails.eval a c1447 := derived1447 a h
  have h6 : Entails.eval a c1332 := derived1332 a h
  have h7 : Entails.eval a c1336 := derived1336 a h
  have h8 : Entails.eval a c1449 := derived1449 a h
  have h9 : Entails.eval a c413 := h 412 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c687, some c503, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 31) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c1441, c687, c503] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c687 := h 686 (by decide)
  have h2 : Entails.eval a c503 := h 502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1328, some c1441, some c1450, some c37, some c1448, some c70, some c1451, some c566, some c75, some c248, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1452 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 31) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1246, c1328, c1441, c1450, c37, c1448, c70, c1451, c566, c75, c248] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1450 := derived1450 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1448 := derived1448 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c1451 := derived1451 a h
  have h8 : Entails.eval a c566 := h 565 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1441, some c1448, some c1450, some c1452, some c399, some c75, some c80, some c128, some c133, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1453 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 31) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c1328, c1441, c1448, c1450, c1452, c399, c75, c80, c128, c133] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1448 := derived1448 a h
  have h3 : Entails.eval a c1450 := derived1450 a h
  have h4 : Entails.eval a c1452 := derived1452 a h
  have h5 : Entails.eval a c399 := h 398 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c128 := h 127 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1328, some c1453, some c1448, some c92, some c75, some c449, some c564, some c750, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1454 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 31) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c1441, c1328, c1453, c1448, c92, c75, c449, c564, c750] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1453 := derived1453 a h
  have h3 : Entails.eval a c1448 := derived1448 a h
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c449 := h 448 (by decide)
  have h7 : Entails.eval a c564 := h 563 (by decide)
  have h8 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1441, some c1448, some c399, some c1454, some c1453, some c50, some c128, some c170, some c883, some c843, some c487, some c450, some c967, some c407, some c596, some c248, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1455 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 31) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c1328, c1441, c1448, c399, c1454, c1453, c50, c128, c170, c883, c843, c487, c450, c967, c407, c596, c248] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1448 := derived1448 a h
  have h3 : Entails.eval a c399 := h 398 (by decide)
  have h4 : Entails.eval a c1454 := derived1454 a h
  have h5 : Entails.eval a c1453 := derived1453 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c883 := h 882 (by decide)
  have h10 : Entails.eval a c843 := h 842 (by decide)
  have h11 : Entails.eval a c487 := h 486 (by decide)
  have h12 : Entails.eval a c450 := h 449 (by decide)
  have h13 : Entails.eval a c967 := derived967 a h
  have h14 : Entails.eval a c407 := h 406 (by decide)
  have h15 : Entails.eval a c596 := h 595 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1328, some c1453, some c1448, some c399, some c1454, some c1455, some c85, some c65, some c551, some c370, some c471, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1456 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 31) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c1441, c1328, c1453, c1448, c399, c1454, c1455, c85, c65, c551, c370, c471] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1453 := derived1453 a h
  have h3 : Entails.eval a c1448 := derived1448 a h
  have h4 : Entails.eval a c399 := h 398 (by decide)
  have h5 : Entails.eval a c1454 := derived1454 a h
  have h6 : Entails.eval a c1455 := derived1455 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c551 := h 550 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c471 := h 470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1457 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1440, some c1441, some c1328, some c499, some c1332, some c1336, some c210, some c392, some c892, some c551, some c632, some c816, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1457 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 31) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c1246, c1440, c1441, c1328, c499, c1332, c1336, c210, c392, c892, c551, c632, c816] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1328 := derived1328 a h
  have h4 : Entails.eval a c499 := h 498 (by decide)
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c892 := h 891 (by decide)
  have h10 : Entails.eval a c551 := h 550 (by decide)
  have h11 : Entails.eval a c632 := h 631 (by decide)
  have h12 : Entails.eval a c816 := h 815 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1328, some c1448, some c1453, some c1456, some c1457, some c92, some c85, some c449, some c564, some c750, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1458 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 31) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c1441, c1328, c1448, c1453, c1456, c1457, c92, c85, c449, c564, c750] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1448 := derived1448 a h
  have h3 : Entails.eval a c1453 := derived1453 a h
  have h4 : Entails.eval a c1456 := derived1456 a h
  have h5 : Entails.eval a c1457 := derived1457 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c449 := h 448 (by decide)
  have h9 : Entails.eval a c564 := h 563 (by decide)
  have h10 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1440, some c121, some c92, some c209, some c392, some c1332, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1459 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 31) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c1328, c1246, c1440, c121, c92, c209, c392, c1332] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c392 := h 391 (by decide)
  have h7 : Entails.eval a c1332 := derived1332 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1460 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c91, some c125, some c137, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1460 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 31) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c1440, c91, c125, c137] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1461 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1441, some c1458, some c222, some c320, some c50, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1461 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 31) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1440, c1441, c1458, c222, c320, c50] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1441, some c1458, some c1459, some c37, some c70, some c1460, some c1451, some c1461, some c726, some c1343, some c329, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1462 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 31) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c1246, c1441, c1458, c1459, c37, c70, c1460, c1451, c1461, c726, c1343, c329] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1460 := derived1460 a h
  have h7 : Entails.eval a c1451 := derived1451 a h
  have h8 : Entails.eval a c1461 := derived1461 a h
  have h9 : Entails.eval a c726 := h 725 (by decide)
  have h10 : Entails.eval a c1343 := derived1343 a h
  have h11 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c233, some c234, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1463 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 31) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1440, c233, c234] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1464 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1440, some c1328, some c1441, some c1462, some c499, some c1336, some c1458, some c70, some c1463, some c1451, some c112, some c372, some c551, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1464 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 31) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c1246, c1440, c1328, c1441, c1462, c499, c1336, c1458, c70, c1463, c1451, c112, c372, c551] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1462 := derived1462 a h
  have h5 : Entails.eval a c499 := h 498 (by decide)
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c1458 := derived1458 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c1463 := derived1463 a h
  have h10 : Entails.eval a c1451 := derived1451 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c551 := h 550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1246, some c1441, some c1458, some c1462, some c499, some c1332, some c1464, some c37, some c71, some c1457, some c730, some c892, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1465 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 31) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c1440, c1246, c1441, c1458, c1462, c499, c1332, c1464, c37, c71, c1457, c730, c892] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1458 := derived1458 a h
  have h4 : Entails.eval a c1462 := derived1462 a h
  have h5 : Entails.eval a c499 := h 498 (by decide)
  have h6 : Entails.eval a c1332 := derived1332 a h
  have h7 : Entails.eval a c1464 := derived1464 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1457 := derived1457 a h
  have h11 : Entails.eval a c730 := h 729 (by decide)
  have h12 : Entails.eval a c892 := h 891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1458, some c71, some c67, some c1465, some c413, some c797, some c612, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1466 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 31) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c1328, c1246, c1458, c71, c67, c1465, c413, c797, c612] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c1465 := derived1465 a h
  have h6 : Entails.eval a c413 := h 412 (by decide)
  have h7 : Entails.eval a c797 := h 796 (by decide)
  have h8 : Entails.eval a c612 := h 611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1467 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1458, some c1466, some c204, some c1332, some c209, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1467 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 31) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1328, c1458, c1466, c204, c1332, c209] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1458 := derived1458 a h
  have h2 : Entails.eval a c1466 := derived1466 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1441, some c204, some c1332, some c17, some c27, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1468 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 31) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c1328, c1441, c204, c1332, c17, c27] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1440, some c1246, some c1467, some c1465, some c1458, some c37, some c1468, some c390, some c497, some c80, some c61, some c726, some c272, some c539, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1469 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 31) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c1441, c1440, c1246, c1467, c1465, c1458, c37, c1468, c390, c497, c80, c61, c726, c272, c539] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c1467 := derived1467 a h
  have h4 : Entails.eval a c1465 := derived1465 a h
  have h5 : Entails.eval a c1458 := derived1458 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1468 := derived1468 a h
  have h8 : Entails.eval a c390 := h 389 (by decide)
  have h9 : Entails.eval a c497 := h 496 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c726 := h 725 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c539 := h 538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1246, some c1441, some c1328, some c1469, some c1467, some c37, some c476, some c1449, some c526, some c84, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1470 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 31) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1440, c1246, c1441, c1328, c1469, c1467, c37, c476, c1449, c526, c84] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1328 := derived1328 a h
  have h4 : Entails.eval a c1469 := derived1469 a h
  have h5 : Entails.eval a c1467 := derived1467 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c476 := h 475 (by decide)
  have h8 : Entails.eval a c1449 := derived1449 a h
  have h9 : Entails.eval a c526 := h 525 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1246, some c1328, some c390, some c413, some c61, some c77, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1471 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 31) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1441, c1246, c1328, c390, c413, c61, c77] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c413 := h 412 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1246, some c1458, some c1465, some c1467, some c37, some c1468, some c1471, some c624, some c272, some c1470, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1472 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 31) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1440, c1246, c1458, c1465, c1467, c37, c1468, c1471, c624, c272, c1470] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1458 := derived1458 a h
  have h3 : Entails.eval a c1465 := derived1465 a h
  have h4 : Entails.eval a c1467 := derived1467 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c1468 := derived1468 a h
  have h7 : Entails.eval a c1471 := derived1471 a h
  have h8 : Entails.eval a c624 := h 623 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c1470 := derived1470 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1441, some c1440, some c539, some c526, some c1332, some c1336, some c718, some c609, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1473 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 31) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c1246, c1441, c1440, c539, c526, c1332, c1336, c718, c609] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c539 := h 538 (by decide)
  have h4 : Entails.eval a c526 := h 525 (by decide)
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1336 := derived1336 a h
  have h7 : Entails.eval a c718 := h 717 (by decide)
  have h8 : Entails.eval a c609 := h 608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1472, some c54, some c529, some c721, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1474 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 31) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c1441, c1472, c54, c529, c721] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1472 := derived1472 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c529 := h 528 (by decide)
  have h4 : Entails.eval a c721 := h 720 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1441, some c1440, some c1472, some c54, some c1473, some c421, some c1474, some c80, some c77, some c718, some c197, some c201, some c49, some c186, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1475 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 31) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c1328, c1246, c1441, c1440, c1472, c54, c1473, c421, c1474, c80, c77, c718, c197, c201, c49, c186] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1440 := derived1440 a h
  have h4 : Entails.eval a c1472 := derived1472 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c1473 := derived1473 a h
  have h7 : Entails.eval a c421 := h 420 (by decide)
  have h8 : Entails.eval a c1474 := derived1474 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c718 := h 717 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c829, some c653, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1476 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 31) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1328, c829, c653] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c829 := h 828 (by decide)
  have h2 : Entails.eval a c653 := h 652 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c112, some c468, some c368, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1477 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 31) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c1328, c112, c468, c368] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c468 := h 467 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1472, some c1477, some c1476, some c657, some c655, some c200, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1478 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 31) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c1328, c1472, c1477, c1476, c657, c655, c200] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1472 := derived1472 a h
  have h2 : Entails.eval a c1477 := derived1477 a h
  have h3 : Entails.eval a c1476 := derived1476 a h
  have h4 : Entails.eval a c657 := h 656 (by decide)
  have h5 : Entails.eval a c655 := h 654 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1475, some c1472, some c1478, some c414, some c462, some c1332, some c522, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1479 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 31) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c1440, c1475, c1472, c1478, c414, c462, c1332, c522] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1475 := derived1475 a h
  have h2 : Entails.eval a c1472 := derived1472 a h
  have h3 : Entails.eval a c1478 := derived1478 a h
  have h4 : Entails.eval a c414 := h 413 (by decide)
  have h5 : Entails.eval a c462 := h 461 (by decide)
  have h6 : Entails.eval a c1332 := derived1332 a h
  have h7 : Entails.eval a c522 := h 521 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1246, some c1441, some c1472, some c1475, some c9, some c1479, some c82, some c512, some c259, some c272, some c261, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1480 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 31) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c1328, c1246, c1441, c1472, c1475, c9, c1479, c82, c512, c259, c272, c261] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1472 := derived1472 a h
  have h4 : Entails.eval a c1475 := derived1475 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1479 := derived1479 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c512 := h 511 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1481 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1481 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1480, some c1472, some c54, some c9, some c1154, some c598, some c410, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1481 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1481 : lratChecker f1481 p1481 = .success := by decide +kernel
theorem unsat1481 : Unsatisfiable (PosFin 31) f1481 := by
  apply lratCheckerSound f1481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1481
  · intro a ha; simp [p1481] at ha; subst a; trivial
  · exact checked1481
theorem derived1481 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1481 := by
  apply localUnsat_implies_entails f1481 [c1328, c1480, c1472, c54, c9, c1154, c598, c410] c1481 unsat1481 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1480 := derived1480 a h
  have h2 : Entails.eval a c1472 := derived1472 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1154 := derived1154 a h
  have h6 : Entails.eval a c598 := h 597 (by decide)
  have h7 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1482 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1482 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1328, some c1481, some c1480, some c1472, some c500, some c27, some c92, some c85, some c121, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1482 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1482 : lratChecker f1482 p1482 = .success := by decide +kernel
theorem unsat1482 : Unsatisfiable (PosFin 31) f1482 := by
  apply lratCheckerSound f1482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1482
  · intro a ha; simp [p1482] at ha; subst a; trivial
  · exact checked1482
theorem derived1482 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1482 := by
  apply localUnsat_implies_entails f1482 [c1441, c1328, c1481, c1480, c1472, c500, c27, c92, c85, c121] c1482 unsat1482 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c1480 := derived1480 a h
  have h4 : Entails.eval a c1472 := derived1472 a h
  have h5 : Entails.eval a c500 := h 499 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1483 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1483 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1482, some c1481, some c1480, some c1472, some c54, some c6, some c543, some c695, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1483 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1483 : lratChecker f1483 p1483 = .success := by decide +kernel
theorem unsat1483 : Unsatisfiable (PosFin 31) f1483 := by
  apply lratCheckerSound f1483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1483
  · intro a ha; simp [p1483] at ha; subst a; trivial
  · exact checked1483
theorem derived1483 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1483 := by
  apply localUnsat_implies_entails f1483 [c1328, c1482, c1481, c1480, c1472, c54, c6, c543, c695] c1483 unsat1483 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1482 := derived1482 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c1480 := derived1480 a h
  have h4 : Entails.eval a c1472 := derived1472 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c543 := h 542 (by decide)
  have h8 : Entails.eval a c695 := h 694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1484 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1484 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c54, some c1480, some c1481, some c1482, some c1332, some c1483, some c441, some c695, some c510, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1484 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1484 : lratChecker f1484 p1484 = .success := by decide +kernel
theorem unsat1484 : Unsatisfiable (PosFin 31) f1484 := by
  apply lratCheckerSound f1484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1484
  · intro a ha; simp [p1484] at ha; subst a; trivial
  · exact checked1484
theorem derived1484 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1484 := by
  apply localUnsat_implies_entails f1484 [c1328, c54, c1480, c1481, c1482, c1332, c1483, c441, c695, c510] c1484 unsat1484 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c1480 := derived1480 a h
  have h3 : Entails.eval a c1481 := derived1481 a h
  have h4 : Entails.eval a c1482 := derived1482 a h
  have h5 : Entails.eval a c1332 := derived1332 a h
  have h6 : Entails.eval a c1483 := derived1483 a h
  have h7 : Entails.eval a c441 := h 440 (by decide)
  have h8 : Entails.eval a c695 := h 694 (by decide)
  have h9 : Entails.eval a c510 := h 509 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1485 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1485 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1472, some c1484, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1485 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1485 : lratChecker f1485 p1485 = .success := by decide +kernel
theorem unsat1485 : Unsatisfiable (PosFin 31) f1485 := by
  apply lratCheckerSound f1485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1485
  · intro a ha; simp [p1485] at ha; subst a; trivial
  · exact checked1485
theorem derived1485 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1485 := by
  apply localUnsat_implies_entails f1485 [c1472, c1484] c1485 unsat1485 (by rfl) a
  have h0 : Entails.eval a c1472 := derived1472 a h
  have h1 : Entails.eval a c1484 := derived1484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1486 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1486 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1440, some c1328, some c441, some c405, some c410, some c163, some c380, some c695, some c23, some c170, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1486 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1486 : lratChecker f1486 p1486 = .success := by decide +kernel
theorem unsat1486 : Unsatisfiable (PosFin 31) f1486 := by
  apply lratCheckerSound f1486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1486
  · intro a ha; simp [p1486] at ha; subst a; trivial
  · exact checked1486
theorem derived1486 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1486 := by
  apply localUnsat_implies_entails f1486 [c1485, c1440, c1328, c441, c405, c410, c163, c380, c695, c23, c170] c1486 unsat1486 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  have h3 : Entails.eval a c441 := h 440 (by decide)
  have h4 : Entails.eval a c405 := h 404 (by decide)
  have h5 : Entails.eval a c410 := h 409 (by decide)
  have h6 : Entails.eval a c163 := h 162 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c695 := h 694 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1487 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1487 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c264, some c170, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1487 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1487 : lratChecker f1487 p1487 = .success := by decide +kernel
theorem unsat1487 : Unsatisfiable (PosFin 31) f1487 := by
  apply lratCheckerSound f1487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1487
  · intro a ha; simp [p1487] at ha; subst a; trivial
  · exact checked1487
theorem derived1487 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1487 := by
  apply localUnsat_implies_entails f1487 [c1328, c264, c170] c1487 unsat1487 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1488 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1488 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c310, some c1487, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1488 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1488 : lratChecker f1488 p1488 = .success := by decide +kernel
theorem unsat1488 : Unsatisfiable (PosFin 31) f1488 := by
  apply lratCheckerSound f1488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1488
  · intro a ha; simp [p1488] at ha; subst a; trivial
  · exact checked1488
theorem derived1488 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1488 := by
  apply localUnsat_implies_entails f1488 [c310, c1487] c1488 unsat1488 (by rfl) a
  have h0 : Entails.eval a c310 := h 309 (by decide)
  have h1 : Entails.eval a c1487 := derived1487 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1489 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1485, some c1332, some c1486, some c543, some c405, some c336, some c1488, some c695, some c312, some c335, some c507, some c862, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1489 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 31) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c1328, c1485, c1332, c1486, c543, c405, c336, c1488, c695, c312, c335, c507, c862] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1332 := derived1332 a h
  have h3 : Entails.eval a c1486 := derived1486 a h
  have h4 : Entails.eval a c543 := h 542 (by decide)
  have h5 : Entails.eval a c405 := h 404 (by decide)
  have h6 : Entails.eval a c336 := h 335 (by decide)
  have h7 : Entails.eval a c1488 := derived1488 a h
  have h8 : Entails.eval a c695 := h 694 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c507 := h 506 (by decide)
  have h12 : Entails.eval a c862 := h 861 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1246, some c1441, some c1328, some c1489, some c27, some c65, some c530, some c92, some c121, some c426, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1490 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 31) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1485, c1246, c1441, c1328, c1489, c27, c65, c530, c92, c121, c426] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1328 := derived1328 a h
  have h4 : Entails.eval a c1489 := derived1489 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c530 := h 529 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c426 := h 425 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1490, some c1154, some c366, some c92, some c82, some c65, some c1476, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1491 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 31) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c1328, c1490, c1154, c366, c92, c82, c65, c1476] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1490 := derived1490 a h
  have h2 : Entails.eval a c1154 := derived1154 a h
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1476 := derived1476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1491, some c1490, some c1154, some c366, some c92, some c684, some c209, some c1388, some c34, some c353, some c410, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1492 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 31) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c1328, c1491, c1490, c1154, c366, c92, c684, c209, c1388, c34, c353, c410] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1491 := derived1491 a h
  have h2 : Entails.eval a c1490 := derived1490 a h
  have h3 : Entails.eval a c1154 := derived1154 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c684 := h 683 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c1388 := derived1388 a h
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c366, some c92, some c1492, some c1332, some c1336, some c210, some c1476, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 31) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1328, c366, c92, c1492, c1332, c1336, c210, c1476] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c1492 := derived1492 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c1476 := derived1476 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1494 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1154, some c1493, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1494 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 31) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1328, c1154, c1493] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1154 := derived1154 a h
  have h2 : Entails.eval a c1493 := derived1493 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1490, some c1494, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1495 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 31) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c1490, c1494] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c1490 := derived1490 a h
  have h1 : Entails.eval a c1494 := derived1494 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1496 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1440, some c1441, some c1495, some c1332, some c1336, some c413, some c210, some c223, some c892, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 31) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1246, c1440, c1441, c1495, c1332, c1336, c413, c210, c223, c892] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1495 := derived1495 a h
  have h4 : Entails.eval a c1332 := derived1332 a h
  have h5 : Entails.eval a c1336 := derived1336 a h
  have h6 : Entails.eval a c413 := h 412 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c892 := h 891 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1246, some c1441, some c1440, some c1495, some c1496, some c499, some c683, some c322, some c520, some c852, some c1396, some c19, some c123, some c124, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1497 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 31) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1485, c1246, c1441, c1440, c1495, c1496, c499, c683, c322, c520, c852, c1396, c19, c123, c124] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1440 := derived1440 a h
  have h4 : Entails.eval a c1495 := derived1495 a h
  have h5 : Entails.eval a c1496 := derived1496 a h
  have h6 : Entails.eval a c499 := h 498 (by decide)
  have h7 : Entails.eval a c683 := h 682 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c520 := h 519 (by decide)
  have h10 : Entails.eval a c852 := h 851 (by decide)
  have h11 : Entails.eval a c1396 := derived1396 a h
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1485, some c322, some c223, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1498 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 31) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1440, c1485, c322, c223] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1440, some c1328, some c1485, some c1498, some c1495, some c1497, some c92, some c269, some c1332, some c22, some c392, some c552, some c811, some c810, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1499 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 31) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1246, c1440, c1328, c1485, c1498, c1495, c1497, c92, c269, c1332, c22, c392, c552, c811, c810] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  have h3 : Entails.eval a c1485 := derived1485 a h
  have h4 : Entails.eval a c1498 := derived1498 a h
  have h5 : Entails.eval a c1495 := derived1495 a h
  have h6 : Entails.eval a c1497 := derived1497 a h
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c1332 := derived1332 a h
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c392 := h 391 (by decide)
  have h12 : Entails.eval a c552 := h 551 (by decide)
  have h13 : Entails.eval a c811 := h 810 (by decide)
  have h14 : Entails.eval a c810 := h 809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1328, some c679, some c582, some c1488, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1500 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 31) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1485, c1328, c679, c582, c1488] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c679 := h 678 (by decide)
  have h3 : Entails.eval a c582 := h 581 (by decide)
  have h4 : Entails.eval a c1488 := derived1488 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1495, some c1498, some c1499, some c148, some c1500, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1501 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 31) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1441, c1495, c1498, c1499, c148, c1500] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1495 := derived1495 a h
  have h2 : Entails.eval a c1498 := derived1498 a h
  have h3 : Entails.eval a c1499 := derived1499 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c1500 := derived1500 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1328, some c1441, some c1501, some c1488, some c405, some c189, some c644, some c27, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1502 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 31) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1485, c1328, c1441, c1501, c1488, c405, c189, c644, c27] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1328 := derived1328 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1501 := derived1501 a h
  have h4 : Entails.eval a c1488 := derived1488 a h
  have h5 : Entails.eval a c405 := h 404 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c644 := h 643 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1502

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
