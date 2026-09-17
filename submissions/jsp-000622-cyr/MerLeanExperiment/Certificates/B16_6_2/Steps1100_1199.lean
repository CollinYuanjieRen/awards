import MerLeanExperiment.Certificates.B16_6_2.Steps1000_1099

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1493 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c1492, some c110, some c109, some c1213, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 57) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c372, c1492, c110, c109, c1213] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c1492 := derived1492 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1213 := derived1213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1494 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨44, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c307, some c58, some c376, some c291, some c353, some c389, some c1189, some c56, some c142, some c8, some c6, some c169, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 57) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c326, c307, c58, c376, c291, c353, c389, c1189, c56, c142, c8, c6, c169] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c1189 := derived1189 a h
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1493, some c391, some c323, some c1492, some c1494, some c38, some c1405, some c50, some c389, some c328, some c369, some c143, some c300, some c5, some c142, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 57) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c1493, c391, c323, c1492, c1494, c38, c1405, c50, c389, c328, c369, c143, c300, c5, c142] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c1493 := derived1493 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c1492 := derived1492 a h
  have h4 : Entails.eval a c1494 := derived1494 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c1405 := derived1405 a h
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c110, some c1212, some c1445, some c109, some c314, some c146, some c376, some c328, some c324, some c7, some c378, some c114, some c83, some c23, some c21, some c301, some c218, some c242, some c253, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 57) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1489, c110, c1212, c1445, c109, c314, c146, c376, c328, c324, c7, c378, c114, c83, c23, c21, c301, c218, c242, c253] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1212 := derived1212 a h
  have h3 : Entails.eval a c1445 := derived1445 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c378 := h 377 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c242 := h 241 (by decide)
  have h19 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c323, some c1287, some c1493, some c391, some c1495, some c110, some c109, some c1212, some c43, some c1496, some c389, some c369, some c300, some c142, some c180, some c5, some c1216, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 57) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1489, c323, c1287, c1493, c391, c1495, c110, c109, c1212, c43, c1496, c389, c369, c300, c142, c180, c5, c1216] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1493 := derived1493 a h
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c1495 := derived1495 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c1212 := derived1212 a h
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c1496 := derived1496 a h
  have h11 : Entails.eval a c389 := h 388 (by decide)
  have h12 : Entails.eval a c369 := h 368 (by decide)
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  have h15 : Entails.eval a c180 := h 179 (by decide)
  have h16 : Entails.eval a c5 := h 4 (by decide)
  have h17 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1287, some c372, some c1151, some c305, some c149, some c58, some c376, some c176, some c342, some c53, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 57) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1489, c1287, c372, c1151, c305, c149, c58, c376, c176, c342, c53] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1151 := derived1151 a h
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c342 := h 341 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c372, some c1287, some c1498, some c50, some c1273, some c304, some c378, some c57, some c53, some c341, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 57) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1489, c372, c1287, c1498, c50, c1273, c304, c378, c57, c53, c341] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1498 := derived1498 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c1273 := derived1273 a h
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1497, some c1210, some c1215, some c8, some c110, some c79, some c1220, some c372, some c1062, some c1499, some c321, some c50, some c1151, some c305, some c152, some c90, some c184, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 57) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1497, c1210, c1215, c8, c110, c79, c1220, c372, c1062, c1499, c321, c50, c1151, c305, c152, c90, c184] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1497 := derived1497 a h
  have h1 : Entails.eval a c1210 := derived1210 a h
  have h2 : Entails.eval a c1215 := derived1215 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c1220 := derived1220 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c1062 := derived1062 a h
  have h9 : Entails.eval a c1499 := derived1499 a h
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c1151 := derived1151 a h
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c1497, some c1210, some c1215, some c1173, some c110, some c8, some c193, some c1500, some c1375, some c389, some c187, some c78, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 57) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c79, c1497, c1210, c1215, c1173, c110, c8, c193, c1500, c1375, c389, c187, c78] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c1497 := derived1497 a h
  have h2 : Entails.eval a c1210 := derived1210 a h
  have h3 : Entails.eval a c1215 := derived1215 a h
  have h4 : Entails.eval a c1173 := derived1173 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c1500 := derived1500 a h
  have h9 : Entails.eval a c1375 := derived1375 a h
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c323, some c1287, some c41, some c300, some c74, some c54, some c81, some c84, some c284, some c378, some c376, some c389, some c347, some c372, some c226, some c340, some c383, some c254, some c334, some c113, some c364, some c176, some c173, some c171, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 57) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1489, c323, c1287, c41, c300, c74, c54, c81, c84, c284, c378, c376, c389, c347, c372, c226, c340, c383, c254, c334, c113, c364, c176, c173, c171] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c340 := h 339 (by decide)
  have h17 : Entails.eval a c383 := h 382 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  have h19 : Entails.eval a c334 := h 333 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c364 := h 363 (by decide)
  have h22 : Entails.eval a c176 := h 175 (by decide)
  have h23 : Entails.eval a c173 := h 172 (by decide)
  have h24 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1501, some c1502, some c1210, some c79, some c1062, some c372, some c1220, some c1215, some c41, some c1499, some c1151, some c206, some c1447, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 57) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1489, c1501, c1502, c1210, c79, c1062, c372, c1220, c1215, c41, c1499, c1151, c206, c1447] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1501 := derived1501 a h
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c1210 := derived1210 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1062 := derived1062 a h
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c1220 := derived1220 a h
  have h8 : Entails.eval a c1215 := derived1215 a h
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c1499 := derived1499 a h
  have h11 : Entails.eval a c1151 := derived1151 a h
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c1447 := derived1447 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1501, some c1503, some c321, some c50, some c44, some c1151, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 57) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1501, c1503, c321, c50, c44, c1151] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1501 := derived1501 a h
  have h1 : Entails.eval a c1503 := derived1503 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c1151 := derived1151 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c298, some c1156, some c84, some c304, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 57) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c298, c1156, c84, c304] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c298 := h 297 (by decide)
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c41, some c44, some c321, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 57) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c1489, c41, c44, c321] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1501, some c1506, some c1502, some c1215, some c1210, some c1220, some c372, some c1504, some c1505, some c15, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 57) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1501, c1506, c1502, c1215, c1210, c1220, c372, c1504, c1505, c15] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1501 := derived1501 a h
  have h1 : Entails.eval a c1506 := derived1506 a h
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c1215 := derived1215 a h
  have h4 : Entails.eval a c1210 := derived1210 a h
  have h5 : Entails.eval a c1220 := derived1220 a h
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c1504 := derived1504 a h
  have h8 : Entails.eval a c1505 := derived1505 a h
  have h9 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c376, some c58, some c283, some c342, some c61, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 57) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1489, c376, c58, c283, c342, c61] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c378, some c382, some c81, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 57) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1489, c378, c382, c81] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c1501, some c1502, some c1215, some c1173, some c1507, some c1509, some c376, some c389, some c74, some c193, some c180, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 57) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c79, c1501, c1502, c1215, c1173, c1507, c1509, c376, c389, c74, c193, c180] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c1501 := derived1501 a h
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c1215 := derived1215 a h
  have h4 : Entails.eval a c1173 := derived1173 a h
  have h5 : Entails.eval a c1507 := derived1507 a h
  have h6 : Entails.eval a c1509 := derived1509 a h
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c37, some c77, some c1214, some c110, some c108, some c102, some c43, some c304, some c76, some c56, some c83, some c353, some c378, some c58, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 57) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c1489, c37, c77, c1214, c110, c108, c102, c43, c304, c76, c56, c83, c353, c378, c58] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c1214 := derived1214 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨31, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1510, some c77, some c37, some c321, some c328, some c42, some c1511, some c1502, some c1509, some c96, some c376, some c389, some c1220, some c372, some c304, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 57) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c1489, c1510, c77, c37, c321, c328, c42, c1511, c1502, c1509, c96, c376, c389, c1220, c372, c304] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1510 := derived1510 a h
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c1511 := derived1511 a h
  have h8 : Entails.eval a c1502 := derived1502 a h
  have h9 : Entails.eval a c1509 := derived1509 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c1220 := derived1220 a h
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨8, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c53, some c73, some c110, some c108, some c50, some c70, some c83, some c342, some c278, some c78, some c43, some c305, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 57) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c1489, c53, c73, c110, c108, c50, c70, c83, c342, c278, c78, c43, c305] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c342 := h 341 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c70, some c283, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 57) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c50, c70, c283] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨48, by decide⟩, false), (⟨31, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1512, some c308, some c379, some c490, some c1210, some c1215, some c73, some c53, some c188, some c341, some c57, some c306, some c384, some c82, some c1513, some c1506, some c81, some c64, some c180, some c1514, some c15, some c1375, some c1156, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 57) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c1489, c1512, c308, c379, c490, c1210, c1215, c73, c53, c188, c341, c57, c306, c384, c82, c1513, c1506, c81, c64, c180, c1514, c15, c1375, c1156] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1512 := derived1512 a h
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c490 := derived490 a h
  have h5 : Entails.eval a c1210 := derived1210 a h
  have h6 : Entails.eval a c1215 := derived1215 a h
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c341 := h 340 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c384 := h 383 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c1513 := derived1513 a h
  have h16 : Entails.eval a c1506 := derived1506 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c180 := h 179 (by decide)
  have h20 : Entails.eval a c1514 := derived1514 a h
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c1375 := derived1375 a h
  have h23 : Entails.eval a c1156 := derived1156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨25, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c42, some c1287, some c376, some c86, some c58, some c380, some c342, some c369, some c62, some c347, some c287, some c333, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 57) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c1489, c42, c1287, c376, c86, c58, c380, c342, c369, c62, c347, c287, c333] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c372, some c1515, some c79, some c112, some c323, some c42, some c1516, some c307, some c378, some c82, some c301, some c144, some c1171, some c185, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 57) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1489, c372, c1515, c79, c112, c323, c42, c1516, c307, c378, c82, c301, c144, c1171, c185] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c1515 := derived1515 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c323 := h 322 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c1171 := derived1171 a h
  have h14 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c86, some c58, some c380, some c301, some c181, some c347, some c35, some c115, some c222, some c257, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 57) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c376, c86, c58, c380, c301, c181, c347, c35, c115, c222, c257] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c347 := h 346 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1515, some c79, some c112, some c372, some c1517, some c1210, some c1215, some c1173, some c1220, some c1062, some c8, some c193, some c1518, some c378, some c305, some c82, some c46, some c301, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 57) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c1489, c1515, c79, c112, c372, c1517, c1210, c1215, c1173, c1220, c1062, c8, c193, c1518, c378, c305, c82, c46, c301] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1515 := derived1515 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c1517 := derived1517 a h
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1173 := derived1173 a h
  have h9 : Entails.eval a c1220 := derived1220 a h
  have h10 : Entails.eval a c1062 := derived1062 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  have h13 : Entails.eval a c1518 := derived1518 a h
  have h14 : Entails.eval a c378 := h 377 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c46 := h 45 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1515, some c79, some c112, some c1519, some c391, some c75, some c1212, some c35, some c98, some c389, some c369, some c297, some c142, some c8, some c177, some c1216, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 57) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c1515, c79, c112, c1519, c391, c75, c1212, c35, c98, c389, c369, c297, c142, c8, c177, c1216] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c1515 := derived1515 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1519 := derived1519 a h
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c1212 := derived1212 a h
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c142 := h 141 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  have h15 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1521 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1515, some c79, some c112, some c1520, some c110, some c109, some c1212, some c1213, some c391, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1521 : lratChecker f1521 p1521 = .success := by decide +kernel
theorem unsat1521 : Unsatisfiable (PosFin 57) f1521 := by
  apply lratCheckerSound f1521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1521
  · intro a ha; simp [p1521] at ha; subst a; trivial
  · exact checked1521
theorem derived1521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1521 := by
  apply localUnsat_implies_entails f1521 [c1515, c79, c112, c1520, c110, c109, c1212, c1213, c391] c1521 unsat1521 (by rfl) a
  have h0 : Entails.eval a c1515 := derived1515 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1520 := derived1520 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c1212 := derived1212 a h
  have h7 : Entails.eval a c1213 := derived1213 a h
  have h8 : Entails.eval a c391 := h 390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1522 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c312, some c300, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1522 : lratChecker f1522 p1522 = .success := by decide +kernel
theorem unsat1522 : Unsatisfiable (PosFin 57) f1522 := by
  apply lratCheckerSound f1522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1522
  · intro a ha; simp [p1522] at ha; subst a; trivial
  · exact checked1522
theorem derived1522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1522 := by
  apply localUnsat_implies_entails f1522 [c369, c312, c300] c1522 unsat1522 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1523 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c388, some c98, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1523 : lratChecker f1523 p1523 = .success := by decide +kernel
theorem unsat1523 : Unsatisfiable (PosFin 57) f1523 := by
  apply lratCheckerSound f1523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1523
  · intro a ha; simp [p1523] at ha; subst a; trivial
  · exact checked1523
theorem derived1523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1523 := by
  apply localUnsat_implies_entails f1523 [c389, c388, c98] c1523 unsat1523 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1524 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1515, some c79, some c112, some c323, some c1522, some c42, some c328, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1524 : lratChecker f1524 p1524 = .success := by decide +kernel
theorem unsat1524 : Unsatisfiable (PosFin 57) f1524 := by
  apply lratCheckerSound f1524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1524
  · intro a ha; simp [p1524] at ha; subst a; trivial
  · exact checked1524
theorem derived1524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1524 := by
  apply localUnsat_implies_entails f1524 [c1489, c1515, c79, c112, c323, c1522, c42, c328] c1524 unsat1524 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1515 := derived1515 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c1522 := derived1522 a h
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1525 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1521, some c79, some c1524, some c1210, some c1215, some c1173, some c8, some c193, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1525 : lratChecker f1525 p1525 = .success := by decide +kernel
theorem unsat1525 : Unsatisfiable (PosFin 57) f1525 := by
  apply lratCheckerSound f1525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1525
  · intro a ha; simp [p1525] at ha; subst a; trivial
  · exact checked1525
theorem derived1525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1525 := by
  apply localUnsat_implies_entails f1525 [c1521, c79, c1524, c1210, c1215, c1173, c8, c193] c1525 unsat1525 (by rfl) a
  have h0 : Entails.eval a c1521 := derived1521 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c1524 := derived1524 a h
  have h3 : Entails.eval a c1210 := derived1210 a h
  have h4 : Entails.eval a c1215 := derived1215 a h
  have h5 : Entails.eval a c1173 := derived1173 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1526 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1525, some c1515, some c79, some c112, some c1519, some c1523, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1526 : lratChecker f1526 p1526 = .success := by decide +kernel
theorem unsat1526 : Unsatisfiable (PosFin 57) f1526 := by
  apply lratCheckerSound f1526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1526
  · intro a ha; simp [p1526] at ha; subst a; trivial
  · exact checked1526
theorem derived1526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1526 := by
  apply localUnsat_implies_entails f1526 [c1525, c1515, c79, c112, c1519, c1523] c1526 unsat1526 (by rfl) a
  have h0 : Entails.eval a c1525 := derived1525 a h
  have h1 : Entails.eval a c1515 := derived1515 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1519 := derived1519 a h
  have h5 : Entails.eval a c1523 := derived1523 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1527 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1515, some c79, some c112, some c1525, some c1526, some c110, some c109, some c1212, some c1213, some c388, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1527 : lratChecker f1527 p1527 = .success := by decide +kernel
theorem unsat1527 : Unsatisfiable (PosFin 57) f1527 := by
  apply lratCheckerSound f1527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1527
  · intro a ha; simp [p1527] at ha; subst a; trivial
  · exact checked1527
theorem derived1527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1527 := by
  apply localUnsat_implies_entails f1527 [c1515, c79, c112, c1525, c1526, c110, c109, c1212, c1213, c388] c1527 unsat1527 (by rfl) a
  have h0 : Entails.eval a c1515 := derived1515 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1525 := derived1525 a h
  have h4 : Entails.eval a c1526 := derived1526 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1212 := derived1212 a h
  have h8 : Entails.eval a c1213 := derived1213 a h
  have h9 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1528 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1527, some c1509, some c1515, some c79, some c112, some c86, some c372, some c1517, some c380, some c1210, some c1220, some c74, some c1062, some c1518, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1528 : lratChecker f1528 p1528 = .success := by decide +kernel
theorem unsat1528 : Unsatisfiable (PosFin 57) f1528 := by
  apply lratCheckerSound f1528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1528
  · intro a ha; simp [p1528] at ha; subst a; trivial
  · exact checked1528
theorem derived1528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1528 := by
  apply localUnsat_implies_entails f1528 [c1527, c1509, c1515, c79, c112, c86, c372, c1517, c380, c1210, c1220, c74, c1062, c1518] c1528 unsat1528 (by rfl) a
  have h0 : Entails.eval a c1527 := derived1527 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c1515 := derived1515 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c1517 := derived1517 a h
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c1210 := derived1210 a h
  have h10 : Entails.eval a c1220 := derived1220 a h
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c1062 := derived1062 a h
  have h13 : Entails.eval a c1518 := derived1518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1529 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1527, some c1509, some c1515, some c79, some c112, some c86, some c1528, some c1523, some c93, some c34, some c74, some c1508, some c297, some c46, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1529 : lratChecker f1529 p1529 = .success := by decide +kernel
theorem unsat1529 : Unsatisfiable (PosFin 57) f1529 := by
  apply lratCheckerSound f1529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1529
  · intro a ha; simp [p1529] at ha; subst a; trivial
  · exact checked1529
theorem derived1529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1529 := by
  apply localUnsat_implies_entails f1529 [c1489, c1527, c1509, c1515, c79, c112, c86, c1528, c1523, c93, c34, c74, c1508, c297, c46] c1529 unsat1529 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1527 := derived1527 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c1515 := derived1515 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c1528 := derived1528 a h
  have h8 : Entails.eval a c1523 := derived1523 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c1508 := derived1508 a h
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1530 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c42, some c41, some c328, some c324, some c1156, some c144, some c36, some c13, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1530 : lratChecker f1530 p1530 = .success := by decide +kernel
theorem unsat1530 : Unsatisfiable (PosFin 57) f1530 := by
  apply lratCheckerSound f1530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1530
  · intro a ha; simp [p1530] at ha; subst a; trivial
  · exact checked1530
theorem derived1530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1530 := by
  apply localUnsat_implies_entails f1530 [c1489, c42, c41, c328, c324, c1156, c144, c36, c13] c1530 unsat1530 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c1156 := derived1156 a h
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1531 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨28, by decide⟩, false), (⟨15, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c301, some c1149, some c55, some c345, some c287, some c285, some c1135, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1531 : lratChecker f1531 p1531 = .success := by decide +kernel
theorem unsat1531 : Unsatisfiable (PosFin 57) f1531 := by
  apply lratCheckerSound f1531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1531
  · intro a ha; simp [p1531] at ha; subst a; trivial
  · exact checked1531
theorem derived1531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1531 := by
  apply localUnsat_implies_entails f1531 [c1489, c301, c1149, c55, c345, c287, c285, c1135] c1531 unsat1531 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c1149 := derived1149 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c285 := h 284 (by decide)
  have h7 : Entails.eval a c1135 := derived1135 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1532 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c181, some c54, some c347, some c345, some c166, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1532 : lratChecker f1532 p1532 = .success := by decide +kernel
theorem unsat1532 : Unsatisfiable (PosFin 57) f1532 := by
  apply lratCheckerSound f1532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1532
  · intro a ha; simp [p1532] at ha; subst a; trivial
  · exact checked1532
theorem derived1532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1532 := by
  apply localUnsat_implies_entails f1532 [c380, c181, c54, c347, c345, c166] c1532 unsat1532 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c181 := h 180 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1533 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1529, some c1527, some c1509, some c376, some c1515, some c79, some c112, some c372, some c1530, some c323, some c321, some c1210, some c1215, some c1173, some c1220, some c1221, some c1062, some c15, some c1156, some c34, some c1531, some c35, some c1532, some c82, some c55, some c345, some c54, some c61, some c180, some c1075, some c165, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1533 : lratChecker f1533 p1533 = .success := by decide +kernel
theorem unsat1533 : Unsatisfiable (PosFin 57) f1533 := by
  apply lratCheckerSound f1533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1533
  · intro a ha; simp [p1533] at ha; subst a; trivial
  · exact checked1533
theorem derived1533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1533 := by
  apply localUnsat_implies_entails f1533 [c1489, c1529, c1527, c1509, c376, c1515, c79, c112, c372, c1530, c323, c321, c1210, c1215, c1173, c1220, c1221, c1062, c15, c1156, c34, c1531, c35, c1532, c82, c55, c345, c54, c61, c180, c1075, c165] c1533 unsat1533 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1527 := derived1527 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c1515 := derived1515 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c1530 := derived1530 a h
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  have h12 : Entails.eval a c1210 := derived1210 a h
  have h13 : Entails.eval a c1215 := derived1215 a h
  have h14 : Entails.eval a c1173 := derived1173 a h
  have h15 : Entails.eval a c1220 := derived1220 a h
  have h16 : Entails.eval a c1221 := derived1221 a h
  have h17 : Entails.eval a c1062 := derived1062 a h
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c1156 := derived1156 a h
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c1531 := derived1531 a h
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c1532 := derived1532 a h
  have h24 : Entails.eval a c82 := h 81 (by decide)
  have h25 : Entails.eval a c55 := h 54 (by decide)
  have h26 : Entails.eval a c345 := h 344 (by decide)
  have h27 : Entails.eval a c54 := h 53 (by decide)
  have h28 : Entails.eval a c61 := h 60 (by decide)
  have h29 : Entails.eval a c180 := h 179 (by decide)
  have h30 : Entails.eval a c1075 := derived1075 a h
  have h31 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1534 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c1527, some c1509, some c376, some c1533, some c389, some c34, some c74, some c300, some c1215, some c1173, some c180, some c193, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1534 : lratChecker f1534 p1534 = .success := by decide +kernel
theorem unsat1534 : Unsatisfiable (PosFin 57) f1534 := by
  apply lratCheckerSound f1534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1534
  · intro a ha; simp [p1534] at ha; subst a; trivial
  · exact checked1534
theorem derived1534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1534 := by
  apply localUnsat_implies_entails f1534 [c79, c1527, c1509, c376, c1533, c389, c34, c74, c300, c1215, c1173, c180, c193] c1534 unsat1534 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c1527 := derived1527 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c1533 := derived1533 a h
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c1215 := derived1215 a h
  have h10 : Entails.eval a c1173 := derived1173 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1535 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨41, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c53, some c1384, some c82, some c303, some c42, some c46, some c279, some c278, some c165, some c66, some c345, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1535 : lratChecker f1535 p1535 = .success := by decide +kernel
theorem unsat1535 : Unsatisfiable (PosFin 57) f1535 := by
  apply lratCheckerSound f1535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1535
  · intro a ha; simp [p1535] at ha; subst a; trivial
  · exact checked1535
theorem derived1535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1535 := by
  apply localUnsat_implies_entails f1535 [c1489, c53, c1384, c82, c303, c42, c46, c279, c278, c165, c66, c345] c1535 unsat1535 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c1384 := derived1384 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1536 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1534, some c308, some c1215, some c188, some c1210, some c379, some c1515, some c110, some c8, some c193, some c1535, some c111, some c112, some c100, some c104, some c389, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1536 : lratChecker f1536 p1536 = .success := by decide +kernel
theorem unsat1536 : Unsatisfiable (PosFin 57) f1536 := by
  apply lratCheckerSound f1536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1536
  · intro a ha; simp [p1536] at ha; subst a; trivial
  · exact checked1536
theorem derived1536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1536 := by
  apply localUnsat_implies_entails f1536 [c1534, c308, c1215, c188, c1210, c379, c1515, c110, c8, c193, c1535, c111, c112, c100, c104, c389] c1536 unsat1536 (by rfl) a
  have h0 : Entails.eval a c1534 := derived1534 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c1215 := derived1215 a h
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c1210 := derived1210 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c1515 := derived1515 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c1535 := derived1535 a h
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1537 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨46, by decide⟩, true), (⟨33, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c58, some c342, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1537 : lratChecker f1537 p1537 = .success := by decide +kernel
theorem unsat1537 : Unsatisfiable (PosFin 57) f1537 := by
  apply lratCheckerSound f1537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1537
  · intro a ha; simp [p1537] at ha; subst a; trivial
  · exact checked1537
theorem derived1537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1537 := by
  apply localUnsat_implies_entails f1537 [c78, c58, c342] c1537 unsat1537 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1538 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1534, some c308, some c379, some c1210, some c1215, some c73, some c53, some c188, some c1536, some c1509, some c81, some c180, some c193, some c1537, some c15, some c200, some c342, some c226, some c172, some c259, some c357, some c114, some c338, some c306, some c1375, some c1156, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1538 : lratChecker f1538 p1538 = .success := by decide +kernel
theorem unsat1538 : Unsatisfiable (PosFin 57) f1538 := by
  apply lratCheckerSound f1538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1538
  · intro a ha; simp [p1538] at ha; subst a; trivial
  · exact checked1538
theorem derived1538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1538 := by
  apply localUnsat_implies_entails f1538 [c1489, c1534, c308, c379, c1210, c1215, c73, c53, c188, c1536, c1509, c81, c180, c193, c1537, c15, c200, c342, c226, c172, c259, c357, c114, c338, c306, c1375, c1156] c1538 unsat1538 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1534 := derived1534 a h
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c1210 := derived1210 a h
  have h5 : Entails.eval a c1215 := derived1215 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c1536 := derived1536 a h
  have h10 : Entails.eval a c1509 := derived1509 a h
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c1537 := derived1537 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c342 := h 341 (by decide)
  have h18 : Entails.eval a c226 := h 225 (by decide)
  have h19 : Entails.eval a c172 := h 171 (by decide)
  have h20 : Entails.eval a c259 := h 258 (by decide)
  have h21 : Entails.eval a c357 := h 356 (by decide)
  have h22 : Entails.eval a c114 := h 113 (by decide)
  have h23 : Entails.eval a c338 := h 337 (by decide)
  have h24 : Entails.eval a c306 := h 305 (by decide)
  have h25 : Entails.eval a c1375 := derived1375 a h
  have h26 : Entails.eval a c1156 := derived1156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1539 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨29, by decide⟩, true), (⟨46, by decide⟩, false), (⟨25, by decide⟩, true), (⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c1156, some c38, some c200, some c305, some c36, some c6, some c149, some c152, some c201, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1539 : lratChecker f1539 p1539 = .success := by decide +kernel
theorem unsat1539 : Unsatisfiable (PosFin 57) f1539 := by
  apply lratCheckerSound f1539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1539
  · intro a ha; simp [p1539] at ha; subst a; trivial
  · exact checked1539
theorem derived1539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1539 := by
  apply localUnsat_implies_entails f1539 [c185, c1156, c38, c200, c305, c36, c6, c149, c152, c201] c1539 unsat1539 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1540 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨12, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1156, some c1223, some c1211, some c149, some c152, some c114, some c201, some c184, some c24, some c259, some c1150, some c251, some c140, some c276, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1540 : lratChecker f1540 p1540 = .success := by decide +kernel
theorem unsat1540 : Unsatisfiable (PosFin 57) f1540 := by
  apply lratCheckerSound f1540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1540
  · intro a ha; simp [p1540] at ha; subst a; trivial
  · exact checked1540
theorem derived1540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1540 := by
  apply localUnsat_implies_entails f1540 [c1156, c1223, c1211, c149, c152, c114, c201, c184, c24, c259, c1150, c251, c140, c276] c1540 unsat1540 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c1223 := derived1223 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c1150 := derived1150 a h
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1541 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1211, some c79, some c1062, some c1223, some c110, some c1318, some c1516, some c42, some c381, some c185, some c328, some c369, some c1539, some c1540, some c6, some c36, some c305, some c1531, some c1172, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1541 : lratChecker f1541 p1541 = .success := by decide +kernel
theorem unsat1541 : Unsatisfiable (PosFin 57) f1541 := by
  apply lratCheckerSound f1541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1541
  · intro a ha; simp [p1541] at ha; subst a; trivial
  · exact checked1541
theorem derived1541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1541 := by
  apply localUnsat_implies_entails f1541 [c1489, c1538, c1211, c79, c1062, c1223, c110, c1318, c1516, c42, c381, c185, c328, c369, c1539, c1540, c6, c36, c305, c1531, c1172] c1541 unsat1541 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1062 := derived1062 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1318 := derived1318 a h
  have h8 : Entails.eval a c1516 := derived1516 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c381 := h 380 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c1539 := derived1539 a h
  have h15 : Entails.eval a c1540 := derived1540 a h
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c305 := h 304 (by decide)
  have h19 : Entails.eval a c1531 := derived1531 a h
  have h20 : Entails.eval a c1172 := derived1172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1542 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c1211, some c79, some c1062, some c1223, some c110, some c1541, some c323, some c321, some c1215, some c1173, some c1220, some c1221, some c8, some c193, some c1531, some c1518, some c46, some c305, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1542 : lratChecker f1542 p1542 = .success := by decide +kernel
theorem unsat1542 : Unsatisfiable (PosFin 57) f1542 := by
  apply lratCheckerSound f1542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1542
  · intro a ha; simp [p1542] at ha; subst a; trivial
  · exact checked1542
theorem derived1542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1542 := by
  apply localUnsat_implies_entails f1542 [c1538, c1211, c79, c1062, c1223, c110, c1541, c323, c321, c1215, c1173, c1220, c1221, c8, c193, c1531, c1518, c46, c305] c1542 unsat1542 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1062 := derived1062 a h
  have h4 : Entails.eval a c1223 := derived1223 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1541 := derived1541 a h
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c1215 := derived1215 a h
  have h10 : Entails.eval a c1173 := derived1173 a h
  have h11 : Entails.eval a c1220 := derived1220 a h
  have h12 : Entails.eval a c1221 := derived1221 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c1531 := derived1531 a h
  have h16 : Entails.eval a c1518 := derived1518 a h
  have h17 : Entails.eval a c46 := h 45 (by decide)
  have h18 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1543 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1273, some c1537, some c58, some c63, some c289, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1543 : lratChecker f1543 p1543 = .success := by decide +kernel
theorem unsat1543 : Unsatisfiable (PosFin 57) f1543 := by
  apply lratCheckerSound f1543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1543
  · intro a ha; simp [p1543] at ha; subst a; trivial
  · exact checked1543
theorem derived1543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1543 := by
  apply localUnsat_implies_entails f1543 [c1489, c1273, c1537, c58, c63, c289] c1543 unsat1543 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1273 := derived1273 a h
  have h2 : Entails.eval a c1537 := derived1537 a h
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1544 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1211, some c110, some c79, some c1223, some c1062, some c1542, some c112, some c108, some c36, some c95, some c1543, some c381, some c185, some c305, some c369, some c38, some c50, some c118, some c328, some c304, some c254, some c259, some c244, some c245, some c276, some c321, some c210, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1544 : lratChecker f1544 p1544 = .success := by decide +kernel
theorem unsat1544 : Unsatisfiable (PosFin 57) f1544 := by
  apply lratCheckerSound f1544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1544
  · intro a ha; simp [p1544] at ha; subst a; trivial
  · exact checked1544
theorem derived1544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1544 := by
  apply localUnsat_implies_entails f1544 [c1489, c1538, c1211, c110, c79, c1223, c1062, c1542, c112, c108, c36, c95, c1543, c381, c185, c305, c369, c38, c50, c118, c328, c304, c254, c259, c244, c245, c276, c321, c210] c1544 unsat1544 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1062 := derived1062 a h
  have h7 : Entails.eval a c1542 := derived1542 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c1543 := derived1543 a h
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c185 := h 184 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c38 := h 37 (by decide)
  have h18 : Entails.eval a c50 := h 49 (by decide)
  have h19 : Entails.eval a c118 := h 117 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c304 := h 303 (by decide)
  have h22 : Entails.eval a c254 := h 253 (by decide)
  have h23 : Entails.eval a c259 := h 258 (by decide)
  have h24 : Entails.eval a c244 := h 243 (by decide)
  have h25 : Entails.eval a c245 := h 244 (by decide)
  have h26 : Entails.eval a c276 := h 275 (by decide)
  have h27 : Entails.eval a c321 := h 320 (by decide)
  have h28 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1545 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨42, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1211, some c110, some c1523, some c1318, some c42, some c391, some c1222, some c297, some c142, some c8, some c177, some c1216, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1545 : lratChecker f1545 p1545 = .success := by decide +kernel
theorem unsat1545 : Unsatisfiable (PosFin 57) f1545 := by
  apply lratCheckerSound f1545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1545
  · intro a ha; simp [p1545] at ha; subst a; trivial
  · exact checked1545
theorem derived1545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1545 := by
  apply localUnsat_implies_entails f1545 [c1489, c1211, c110, c1523, c1318, c42, c391, c1222, c297, c142, c8, c177, c1216] c1545 unsat1545 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1523 := derived1523 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c1222 := derived1222 a h
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  have h12 : Entails.eval a c1216 := derived1216 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1546 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1544, some c1538, some c1211, some c110, some c79, some c1523, some c369, some c1545, some c323, some c1215, some c1173, some c8, some c193, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1546 : lratChecker f1546 p1546 = .success := by decide +kernel
theorem unsat1546 : Unsatisfiable (PosFin 57) f1546 := by
  apply lratCheckerSound f1546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1546
  · intro a ha; simp [p1546] at ha; subst a; trivial
  · exact checked1546
theorem derived1546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1546 := by
  apply localUnsat_implies_entails f1546 [c1544, c1538, c1211, c110, c79, c1523, c369, c1545, c323, c1215, c1173, c8, c193] c1546 unsat1546 (by rfl) a
  have h0 : Entails.eval a c1544 := derived1544 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1523 := derived1523 a h
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c1545 := derived1545 a h
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c1215 := derived1215 a h
  have h10 : Entails.eval a c1173 := derived1173 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1547 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨54, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c110, some c78, some c38, some c305, some c56, some c1057, some c289, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1547 : lratChecker f1547 p1547 = .success := by decide +kernel
theorem unsat1547 : Unsatisfiable (PosFin 57) f1547 := by
  apply lratCheckerSound f1547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1547
  · intro a ha; simp [p1547] at ha; subst a; trivial
  · exact checked1547
theorem derived1547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1547 := by
  apply localUnsat_implies_entails f1547 [c1211, c110, c78, c38, c305, c56, c1057, c289] c1547 unsat1547 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c1057 := derived1057 a h
  have h7 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1548 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c108, some c112, some c1211, some c110, some c102, some c38, some c78, some c575, some c1547, some c43, some c321, some c294, some c1513, some c53, some c341, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1548 : lratChecker f1548 p1548 = .success := by decide +kernel
theorem unsat1548 : Unsatisfiable (PosFin 57) f1548 := by
  apply lratCheckerSound f1548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1548
  · intro a ha; simp [p1548] at ha; subst a; trivial
  · exact checked1548
theorem derived1548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1548 := by
  apply localUnsat_implies_entails f1548 [c1489, c108, c112, c1211, c110, c102, c38, c78, c575, c1547, c43, c321, c294, c1513, c53, c341] c1548 unsat1548 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c1547 := derived1547 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  have h13 : Entails.eval a c1513 := derived1513 a h
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1549 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c353, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1549 : lratChecker f1549 p1549 = .success := by decide +kernel
theorem unsat1549 : Unsatisfiable (PosFin 57) f1549 := by
  apply lratCheckerSound f1549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1549
  · intro a ha; simp [p1549] at ha; subst a; trivial
  · exact checked1549
theorem derived1549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1549 := by
  apply localUnsat_implies_entails f1549 [c1057, c353] c1549 unsat1549 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1550 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c79, some c1538, some c1211, some c110, some c1544, some c1546, some c108, some c1548, some c389, some c369, some c1549, some c56, some c63, some c381, some c380, some c1537, some c1052, some c1287, some c227, some c279, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1550 : lratChecker f1550 p1550 = .success := by decide +kernel
theorem unsat1550 : Unsatisfiable (PosFin 57) f1550 := by
  apply lratCheckerSound f1550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1550
  · intro a ha; simp [p1550] at ha; subst a; trivial
  · exact checked1550
theorem derived1550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1550 := by
  apply localUnsat_implies_entails f1550 [c1489, c79, c1538, c1211, c110, c1544, c1546, c108, c1548, c389, c369, c1549, c56, c63, c381, c380, c1537, c1052, c1287, c227, c279] c1550 unsat1550 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1544 := derived1544 a h
  have h6 : Entails.eval a c1546 := derived1546 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c1548 := derived1548 a h
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c1549 := derived1549 a h
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c381 := h 380 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c1537 := derived1537 a h
  have h17 : Entails.eval a c1052 := derived1052 a h
  have h18 : Entails.eval a c1287 := derived1287 a h
  have h19 : Entails.eval a c227 := h 226 (by decide)
  have h20 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1551 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1211, some c79, some c1062, some c1223, some c1550, some c41, some c42, some c1516, some c1151, some c324, some c185, some c1171, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1551 : lratChecker f1551 p1551 = .success := by decide +kernel
theorem unsat1551 : Unsatisfiable (PosFin 57) f1551 := by
  apply lratCheckerSound f1551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1551
  · intro a ha; simp [p1551] at ha; subst a; trivial
  · exact checked1551
theorem derived1551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1551 := by
  apply localUnsat_implies_entails f1551 [c1489, c1538, c1211, c79, c1062, c1223, c1550, c41, c42, c1516, c1151, c324, c185, c1171] c1551 unsat1551 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1062 := derived1062 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1550 := derived1550 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c1151 := derived1151 a h
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c1171 := derived1171 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1552 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1551, some c323, some c321, some c1221, some c1220, some c79, some c1173, some c1538, some c1211, some c1062, some c1223, some c1518, some c1531, some c305, some c46, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1552 : lratChecker f1552 p1552 = .success := by decide +kernel
theorem unsat1552 : Unsatisfiable (PosFin 57) f1552 := by
  apply lratCheckerSound f1552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1552
  · intro a ha; simp [p1552] at ha; subst a; trivial
  · exact checked1552
theorem derived1552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1552 := by
  apply localUnsat_implies_entails f1552 [c1551, c323, c321, c1221, c1220, c79, c1173, c1538, c1211, c1062, c1223, c1518, c1531, c305, c46] c1552 unsat1552 (by rfl) a
  have h0 : Entails.eval a c1551 := derived1551 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1220 := derived1220 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c1173 := derived1173 a h
  have h7 : Entails.eval a c1538 := derived1538 a h
  have h8 : Entails.eval a c1211 := derived1211 a h
  have h9 : Entails.eval a c1062 := derived1062 a h
  have h10 : Entails.eval a c1223 := derived1223 a h
  have h11 : Entails.eval a c1518 := derived1518 a h
  have h12 : Entails.eval a c1531 := derived1531 a h
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1553 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c1211, some c79, some c1062, some c1223, some c1550, some c1551, some c323, some c1173, some c1552, some c193, some c74, some c178, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1553 : lratChecker f1553 p1553 = .success := by decide +kernel
theorem unsat1553 : Unsatisfiable (PosFin 57) f1553 := by
  apply lratCheckerSound f1553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1553
  · intro a ha; simp [p1553] at ha; subst a; trivial
  · exact checked1553
theorem derived1553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1553 := by
  apply localUnsat_implies_entails f1553 [c1538, c1211, c79, c1062, c1223, c1550, c1551, c323, c1173, c1552, c193, c74, c178] c1553 unsat1553 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1062 := derived1062 a h
  have h4 : Entails.eval a c1223 := derived1223 a h
  have h5 : Entails.eval a c1550 := derived1550 a h
  have h6 : Entails.eval a c1551 := derived1551 a h
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c1173 := derived1173 a h
  have h9 : Entails.eval a c1552 := derived1552 a h
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1554 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1211, some c79, some c1062, some c1223, some c1550, some c1553, some c1530, some c323, some c321, some c1215, some c1173, some c1220, some c1221, some c15, some c1156, some c200, some c34, some c1531, some c35, some c1532, some c1052, some c55, some c227, some c345, some c279, some c61, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1554 : lratChecker f1554 p1554 = .success := by decide +kernel
theorem unsat1554 : Unsatisfiable (PosFin 57) f1554 := by
  apply lratCheckerSound f1554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1554
  · intro a ha; simp [p1554] at ha; subst a; trivial
  · exact checked1554
theorem derived1554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1554 := by
  apply localUnsat_implies_entails f1554 [c1489, c1538, c1211, c79, c1062, c1223, c1550, c1553, c1530, c323, c321, c1215, c1173, c1220, c1221, c15, c1156, c200, c34, c1531, c35, c1532, c1052, c55, c227, c345, c279, c61] c1554 unsat1554 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1062 := derived1062 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1550 := derived1550 a h
  have h7 : Entails.eval a c1553 := derived1553 a h
  have h8 : Entails.eval a c1530 := derived1530 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1173 := derived1173 a h
  have h13 : Entails.eval a c1220 := derived1220 a h
  have h14 : Entails.eval a c1221 := derived1221 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c1156 := derived1156 a h
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c1531 := derived1531 a h
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c1532 := derived1532 a h
  have h22 : Entails.eval a c1052 := derived1052 a h
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c227 := h 226 (by decide)
  have h25 : Entails.eval a c345 := h 344 (by decide)
  have h26 : Entails.eval a c279 := h 278 (by decide)
  have h27 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1555 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1537, some c58, some c61, some c347, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1555 : lratChecker f1555 p1555 = .success := by decide +kernel
theorem unsat1555 : Unsatisfiable (PosFin 57) f1555 := by
  apply lratCheckerSound f1555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1555
  · intro a ha; simp [p1555] at ha; subst a; trivial
  · exact checked1555
theorem derived1555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1555 := by
  apply localUnsat_implies_entails f1555 [c1489, c1537, c58, c61, c347] c1555 unsat1555 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1537 := derived1537 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1556 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1151, some c1505, some c1171, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1556 : lratChecker f1556 p1556 = .success := by decide +kernel
theorem unsat1556 : Unsatisfiable (PosFin 57) f1556 := by
  apply lratCheckerSound f1556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1556
  · intro a ha; simp [p1556] at ha; subst a; trivial
  · exact checked1556
theorem derived1556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1556 := by
  apply localUnsat_implies_entails f1556 [c1151, c1505, c1171] c1556 unsat1556 (by rfl) a
  have h0 : Entails.eval a c1151 := derived1151 a h
  have h1 : Entails.eval a c1505 := derived1505 a h
  have h2 : Entails.eval a c1171 := derived1171 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1557 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨46, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c321, some c1287, some c1311, some c90, some c383, some c184, some c1222, some c1069, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1557 : lratChecker f1557 p1557 = .success := by decide +kernel
theorem unsat1557 : Unsatisfiable (PosFin 57) f1557 := by
  apply lratCheckerSound f1557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1557
  · intro a ha; simp [p1557] at ha; subst a; trivial
  · exact checked1557
theorem derived1557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1557 := by
  apply localUnsat_implies_entails f1557 [c50, c321, c1287, c1311, c90, c383, c184, c1222, c1069] c1557 unsat1557 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1311 := derived1311 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  have h7 : Entails.eval a c1222 := derived1222 a h
  have h8 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1558 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1550, some c79, some c1538, some c1211, some c1223, some c1062, some c1554, some c112, some c1506, some c1151, some c1556, some c185, some c1557, some c13, some c15, some c36, some c95, some c1215, some c1094, some c298, some c323, some c84, some c1311, some c184, some c1069, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1558 : lratChecker f1558 p1558 = .success := by decide +kernel
theorem unsat1558 : Unsatisfiable (PosFin 57) f1558 := by
  apply lratCheckerSound f1558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1558
  · intro a ha; simp [p1558] at ha; subst a; trivial
  · exact checked1558
theorem derived1558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1558 := by
  apply localUnsat_implies_entails f1558 [c1489, c1550, c79, c1538, c1211, c1223, c1062, c1554, c112, c1506, c1151, c1556, c185, c1557, c13, c15, c36, c95, c1215, c1094, c298, c323, c84, c1311, c184, c1069] c1558 unsat1558 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1550 := derived1550 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1538 := derived1538 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1062 := derived1062 a h
  have h7 : Entails.eval a c1554 := derived1554 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1506 := derived1506 a h
  have h10 : Entails.eval a c1151 := derived1151 a h
  have h11 : Entails.eval a c1556 := derived1556 a h
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c1557 := derived1557 a h
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c1215 := derived1215 a h
  have h19 : Entails.eval a c1094 := derived1094 a h
  have h20 : Entails.eval a c298 := h 297 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c84 := h 83 (by decide)
  have h23 : Entails.eval a c1311 := derived1311 a h
  have h24 : Entails.eval a c184 := h 183 (by decide)
  have h25 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1559 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1318, some c42, some c391, some c297, some c1222, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1559 : lratChecker f1559 p1559 = .success := by decide +kernel
theorem unsat1559 : Unsatisfiable (PosFin 57) f1559 := by
  apply lratCheckerSound f1559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1559
  · intro a ha; simp [p1559] at ha; subst a; trivial
  · exact checked1559
theorem derived1559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1559 := by
  apply localUnsat_implies_entails f1559 [c1489, c1318, c42, c391, c297, c1222] c1559 unsat1559 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1318 := derived1318 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c1222 := derived1222 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1560 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1559, some c323, some c321, some c1221, some c391, some c1222, some c35, some c297, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1560 : lratChecker f1560 p1560 = .success := by decide +kernel
theorem unsat1560 : Unsatisfiable (PosFin 57) f1560 := by
  apply lratCheckerSound f1560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1560
  · intro a ha; simp [p1560] at ha; subst a; trivial
  · exact checked1560
theorem derived1560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1560 := by
  apply localUnsat_implies_entails f1560 [c1559, c323, c321, c1221, c391, c1222, c35, c297] c1560 unsat1560 (by rfl) a
  have h0 : Entails.eval a c1559 := derived1559 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1561 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1523, some c34, some c74, some c1560, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1561 : lratChecker f1561 p1561 = .success := by decide +kernel
theorem unsat1561 : Unsatisfiable (PosFin 57) f1561 := by
  apply lratCheckerSound f1561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1561
  · intro a ha; simp [p1561] at ha; subst a; trivial
  · exact checked1561
theorem derived1561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1561 := by
  apply localUnsat_implies_entails f1561 [c1523, c34, c74, c1560] c1561 unsat1561 (by rfl) a
  have h0 : Entails.eval a c1523 := derived1523 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c1560 := derived1560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1562 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1550, some c79, some c1538, some c1558, some c1561, some c112, some c1506, some c389, some c388, some c102, some c38, some c78, some c575, some c326, some c325, some c299, some c1173, some c1219, some c54, some c81, some c200, some c328, some c281, some c346, some c1514, some c174, some c294, some c341, some c163, some c43, some c162, some c9, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1562 : lratChecker f1562 p1562 = .success := by decide +kernel
theorem unsat1562 : Unsatisfiable (PosFin 57) f1562 := by
  apply lratCheckerSound f1562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1562
  · intro a ha; simp [p1562] at ha; subst a; trivial
  · exact checked1562
theorem derived1562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1562 := by
  apply localUnsat_implies_entails f1562 [c1489, c1550, c79, c1538, c1558, c1561, c112, c1506, c389, c388, c102, c38, c78, c575, c326, c325, c299, c1173, c1219, c54, c81, c200, c328, c281, c346, c1514, c174, c294, c341, c163, c43, c162, c9] c1562 unsat1562 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1550 := derived1550 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1538 := derived1538 a h
  have h4 : Entails.eval a c1558 := derived1558 a h
  have h5 : Entails.eval a c1561 := derived1561 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1506 := derived1506 a h
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c575 := derived575 a h
  have h14 : Entails.eval a c326 := h 325 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c1173 := derived1173 a h
  have h18 : Entails.eval a c1219 := derived1219 a h
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  have h21 : Entails.eval a c200 := h 199 (by decide)
  have h22 : Entails.eval a c328 := h 327 (by decide)
  have h23 : Entails.eval a c281 := h 280 (by decide)
  have h24 : Entails.eval a c346 := h 345 (by decide)
  have h25 : Entails.eval a c1514 := derived1514 a h
  have h26 : Entails.eval a c174 := h 173 (by decide)
  have h27 : Entails.eval a c294 := h 293 (by decide)
  have h28 : Entails.eval a c341 := h 340 (by decide)
  have h29 : Entails.eval a c163 := h 162 (by decide)
  have h30 : Entails.eval a c43 := h 42 (by decide)
  have h31 : Entails.eval a c162 := h 161 (by decide)
  have h32 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1563 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1558, some c1550, some c79, some c1538, some c1561, some c112, some c1506, some c1562, some c74, some c96, some c391, some c1222, some c297, some c143, some c177, some c11, some c193, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1563 : lratChecker f1563 p1563 = .success := by decide +kernel
theorem unsat1563 : Unsatisfiable (PosFin 57) f1563 := by
  apply lratCheckerSound f1563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1563
  · intro a ha; simp [p1563] at ha; subst a; trivial
  · exact checked1563
theorem derived1563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1563 := by
  apply localUnsat_implies_entails f1563 [c1558, c1550, c79, c1538, c1561, c112, c1506, c1562, c74, c96, c391, c1222, c297, c143, c177, c11, c193] c1563 unsat1563 (by rfl) a
  have h0 : Entails.eval a c1558 := derived1558 a h
  have h1 : Entails.eval a c1550 := derived1550 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1538 := derived1538 a h
  have h4 : Entails.eval a c1561 := derived1561 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1506 := derived1506 a h
  have h7 : Entails.eval a c1562 := derived1562 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c1222 := derived1222 a h
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1564 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨36, by decide⟩, true), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c326, some c284, some c337, some c784, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1564 : lratChecker f1564 p1564 = .success := by decide +kernel
theorem unsat1564 : Unsatisfiable (PosFin 57) f1564 := by
  apply lratCheckerSound f1564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1564
  · intro a ha; simp [p1564] at ha; subst a; trivial
  · exact checked1564
theorem derived1564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1564 := by
  apply localUnsat_implies_entails f1564 [c1211, c326, c284, c337, c784] c1564 unsat1564 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c337 := h 336 (by decide)
  have h4 : Entails.eval a c784 := derived784 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1565 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1215, some c1173, some c15, some c200, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1565 : lratChecker f1565 p1565 = .success := by decide +kernel
theorem unsat1565 : Unsatisfiable (PosFin 57) f1565 := by
  apply lratCheckerSound f1565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1565
  · intro a ha; simp [p1565] at ha; subst a; trivial
  · exact checked1565
theorem derived1565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1565 := by
  apply localUnsat_implies_entails f1565 [c1215, c1173, c15, c200] c1565 unsat1565 (by rfl) a
  have h0 : Entails.eval a c1215 := derived1215 a h
  have h1 : Entails.eval a c1173 := derived1173 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1566 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1563, some c1558, some c1550, some c79, some c1538, some c1211, some c389, some c376, some c1565, some c323, some c41, some c1560, some c54, some c346, some c1564, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1566 : lratChecker f1566 p1566 = .success := by decide +kernel
theorem unsat1566 : Unsatisfiable (PosFin 57) f1566 := by
  apply lratCheckerSound f1566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1566
  · intro a ha; simp [p1566] at ha; subst a; trivial
  · exact checked1566
theorem derived1566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1566 := by
  apply localUnsat_implies_entails f1566 [c1489, c1563, c1558, c1550, c79, c1538, c1211, c389, c376, c1565, c323, c41, c1560, c54, c346, c1564] c1566 unsat1566 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1563 := derived1563 a h
  have h2 : Entails.eval a c1558 := derived1558 a h
  have h3 : Entails.eval a c1550 := derived1550 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1538 := derived1538 a h
  have h6 : Entails.eval a c1211 := derived1211 a h
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c1565 := derived1565 a h
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c1560 := derived1560 a h
  have h13 : Entails.eval a c54 := h 53 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c1564 := derived1564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1567 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1558, some c1550, some c1538, some c1566, some c34, some c74, some c1560, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1567 : lratChecker f1567 p1567 = .success := by decide +kernel
theorem unsat1567 : Unsatisfiable (PosFin 57) f1567 := by
  apply lratCheckerSound f1567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1567
  · intro a ha; simp [p1567] at ha; subst a; trivial
  · exact checked1567
theorem derived1567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1567 := by
  apply localUnsat_implies_entails f1567 [c1558, c1550, c1538, c1566, c34, c74, c1560] c1567 unsat1567 (by rfl) a
  have h0 : Entails.eval a c1558 := derived1558 a h
  have h1 : Entails.eval a c1550 := derived1550 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1566 := derived1566 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c1560 := derived1560 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1568 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1550, some c79, some c1567, some c112, some c1506, some c1563, some c1558, some c1538, some c1211, some c389, some c388, some c1565, some c1222, some c323, some c326, some c1311, some c314, some c146, some c328, some c324, some c297, some c15, some c43, some c1216, some c604, some c9, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1568 : lratChecker f1568 p1568 = .success := by decide +kernel
theorem unsat1568 : Unsatisfiable (PosFin 57) f1568 := by
  apply lratCheckerSound f1568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1568
  · intro a ha; simp [p1568] at ha; subst a; trivial
  · exact checked1568
theorem derived1568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1568 := by
  apply localUnsat_implies_entails f1568 [c1489, c1550, c79, c1567, c112, c1506, c1563, c1558, c1538, c1211, c389, c388, c1565, c1222, c323, c326, c1311, c314, c146, c328, c324, c297, c15, c43, c1216, c604, c9] c1568 unsat1568 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1550 := derived1550 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1567 := derived1567 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1506 := derived1506 a h
  have h6 : Entails.eval a c1563 := derived1563 a h
  have h7 : Entails.eval a c1558 := derived1558 a h
  have h8 : Entails.eval a c1538 := derived1538 a h
  have h9 : Entails.eval a c1211 := derived1211 a h
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c1565 := derived1565 a h
  have h13 : Entails.eval a c1222 := derived1222 a h
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c1311 := derived1311 a h
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c146 := h 145 (by decide)
  have h19 : Entails.eval a c328 := h 327 (by decide)
  have h20 : Entails.eval a c324 := h 323 (by decide)
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c15 := h 14 (by decide)
  have h23 : Entails.eval a c43 := h 42 (by decide)
  have h24 : Entails.eval a c1216 := derived1216 a h
  have h25 : Entails.eval a c604 := derived604 a h
  have h26 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1569 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c79, some c1550, some c1558, some c1567, some c112, some c1506, some c1568, some c74, some c96, some c391, some c1222, some c297, some c143, some c177, some c11, some c193, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1569 : lratChecker f1569 p1569 = .success := by decide +kernel
theorem unsat1569 : Unsatisfiable (PosFin 57) f1569 := by
  apply lratCheckerSound f1569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1569
  · intro a ha; simp [p1569] at ha; subst a; trivial
  · exact checked1569
theorem derived1569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1569 := by
  apply localUnsat_implies_entails f1569 [c1538, c79, c1550, c1558, c1567, c112, c1506, c1568, c74, c96, c391, c1222, c297, c143, c177, c11, c193] c1569 unsat1569 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c1550 := derived1550 a h
  have h3 : Entails.eval a c1558 := derived1558 a h
  have h4 : Entails.eval a c1567 := derived1567 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1506 := derived1506 a h
  have h7 : Entails.eval a c1568 := derived1568 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c1222 := derived1222 a h
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1570 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c323, some c295, some c1220, some c73, some c53, some c82, some c301, some c1537, some c46, some c305, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1570 : lratChecker f1570 p1570 = .success := by decide +kernel
theorem unsat1570 : Unsatisfiable (PosFin 57) f1570 := by
  apply lratCheckerSound f1570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1570
  · intro a ha; simp [p1570] at ha; subst a; trivial
  · exact checked1570
theorem derived1570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1570 := by
  apply localUnsat_implies_entails f1570 [c1489, c323, c295, c1220, c73, c53, c82, c301, c1537, c46, c305] c1570 unsat1570 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c1220 := derived1220 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c1537 := derived1537 a h
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1571 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1223, some c1569, some c1384, some c1570, some c1318, some c42, some c303, some c82, some c86, some c55, some c377, some c381, some c350, some c287, some c225, some c332, some c339, some c1118, some c362, some c174, some c175, some c172, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1571 : lratChecker f1571 p1571 = .success := by decide +kernel
theorem unsat1571 : Unsatisfiable (PosFin 57) f1571 := by
  apply lratCheckerSound f1571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1571
  · intro a ha; simp [p1571] at ha; subst a; trivial
  · exact checked1571
theorem derived1571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1571 := by
  apply localUnsat_implies_entails f1571 [c1489, c1538, c1223, c1569, c1384, c1570, c1318, c42, c303, c82, c86, c55, c377, c381, c350, c287, c225, c332, c339, c1118, c362, c174, c175, c172] c1571 unsat1571 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c1569 := derived1569 a h
  have h4 : Entails.eval a c1384 := derived1384 a h
  have h5 : Entails.eval a c1570 := derived1570 a h
  have h6 : Entails.eval a c1318 := derived1318 a h
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c225 := h 224 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c1118 := derived1118 a h
  have h20 : Entails.eval a c362 := h 361 (by decide)
  have h21 : Entails.eval a c174 := h 173 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1572 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1538, some c1223, some c1569, some c1211, some c110, some c1571, some c108, some c36, some c95, some c100, some c1062, some c112, some c1543, some c305, some c185, some c38, some c50, some c118, some c321, some c328, some c306, some c254, some c154, some c57, some c210, some c11, some c290, some c27, some c127, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1572 : lratChecker f1572 p1572 = .success := by decide +kernel
theorem unsat1572 : Unsatisfiable (PosFin 57) f1572 := by
  apply lratCheckerSound f1572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1572
  · intro a ha; simp [p1572] at ha; subst a; trivial
  · exact checked1572
theorem derived1572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1572 := by
  apply localUnsat_implies_entails f1572 [c1489, c1538, c1223, c1569, c1211, c110, c1571, c108, c36, c95, c100, c1062, c112, c1543, c305, c185, c38, c50, c118, c321, c328, c306, c254, c154, c57, c210, c11, c290, c27, c127] c1572 unsat1572 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1538 := derived1538 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c1569 := derived1569 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1571 := derived1571 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c1062 := derived1062 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c1543 := derived1543 a h
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c118 := h 117 (by decide)
  have h19 : Entails.eval a c321 := h 320 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c306 := h 305 (by decide)
  have h22 : Entails.eval a c254 := h 253 (by decide)
  have h23 : Entails.eval a c154 := h 153 (by decide)
  have h24 : Entails.eval a c57 := h 56 (by decide)
  have h25 : Entails.eval a c210 := h 209 (by decide)
  have h26 : Entails.eval a c11 := h 10 (by decide)
  have h27 : Entails.eval a c290 := h 289 (by decide)
  have h28 : Entails.eval a c27 := h 26 (by decide)
  have h29 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1573 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1572, some c1538, some c1223, some c1569, some c1571, some c1530, some c295, some c82, some c81, some c380, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1573 : lratChecker f1573 p1573 = .success := by decide +kernel
theorem unsat1573 : Unsatisfiable (PosFin 57) f1573 := by
  apply lratCheckerSound f1573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1573
  · intro a ha; simp [p1573] at ha; subst a; trivial
  · exact checked1573
theorem derived1573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1573 := by
  apply localUnsat_implies_entails f1573 [c1489, c1572, c1538, c1223, c1569, c1571, c1530, c295, c82, c81, c380] c1573 unsat1573 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1572 := derived1572 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1223 := derived1223 a h
  have h4 : Entails.eval a c1569 := derived1569 a h
  have h5 : Entails.eval a c1571 := derived1571 a h
  have h6 : Entails.eval a c1530 := derived1530 a h
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1574 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c111, some c100, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1574 : lratChecker f1574 p1574 = .success := by decide +kernel
theorem unsat1574 : Unsatisfiable (PosFin 57) f1574 := by
  apply lratCheckerSound f1574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1574
  · intro a ha; simp [p1574] at ha; subst a; trivial
  · exact checked1574
theorem derived1574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1574 := by
  apply localUnsat_implies_entails f1574 [c112, c111, c100] c1574 unsat1574 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1575 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c306, some c90, some c84, some c381, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1575 : lratChecker f1575 p1575 = .success := by decide +kernel
theorem unsat1575 : Unsatisfiable (PosFin 57) f1575 := by
  apply lratCheckerSound f1575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1575
  · intro a ha; simp [p1575] at ha; subst a; trivial
  · exact checked1575
theorem derived1575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1575 := by
  apply localUnsat_implies_entails f1575 [c50, c306, c90, c84, c381] c1575 unsat1575 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1576 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1569, some c1538, some c1211, some c1223, some c1572, some c1573, some c1574, some c1506, some c1556, some c1151, some c1575, some c15, some c1217, some c13, some c36, some c298, some c81, some c84, some c377, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1576 : lratChecker f1576 p1576 = .success := by decide +kernel
theorem unsat1576 : Unsatisfiable (PosFin 57) f1576 := by
  apply lratCheckerSound f1576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1576
  · intro a ha; simp [p1576] at ha; subst a; trivial
  · exact checked1576
theorem derived1576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1576 := by
  apply localUnsat_implies_entails f1576 [c1489, c1569, c1538, c1211, c1223, c1572, c1573, c1574, c1506, c1556, c1151, c1575, c15, c1217, c13, c36, c298, c81, c84, c377] c1576 unsat1576 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c1223 := derived1223 a h
  have h5 : Entails.eval a c1572 := derived1572 a h
  have h6 : Entails.eval a c1573 := derived1573 a h
  have h7 : Entails.eval a c1574 := derived1574 a h
  have h8 : Entails.eval a c1506 := derived1506 a h
  have h9 : Entails.eval a c1556 := derived1556 a h
  have h10 : Entails.eval a c1151 := derived1151 a h
  have h11 : Entails.eval a c1575 := derived1575 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c1217 := derived1217 a h
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1577 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1318, some c323, some c321, some c1221, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1577 : lratChecker f1577 p1577 = .success := by decide +kernel
theorem unsat1577 : Unsatisfiable (PosFin 57) f1577 := by
  apply lratCheckerSound f1577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1577
  · intro a ha; simp [p1577] at ha; subst a; trivial
  · exact checked1577
theorem derived1577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1577 := by
  apply localUnsat_implies_entails f1577 [c1318, c323, c321, c1221] c1577 unsat1577 (by rfl) a
  have h0 : Entails.eval a c1318 := derived1318 a h
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c1221 := derived1221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1578 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1576, some c1569, some c1538, some c1384, some c391, some c1577, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1578 : lratChecker f1578 p1578 = .success := by decide +kernel
theorem unsat1578 : Unsatisfiable (PosFin 57) f1578 := by
  apply lratCheckerSound f1578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1578
  · intro a ha; simp [p1578] at ha; subst a; trivial
  · exact checked1578
theorem derived1578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1578 := by
  apply localUnsat_implies_entails f1578 [c1576, c1569, c1538, c1384, c391, c1577] c1578 unsat1578 (by rfl) a
  have h0 : Entails.eval a c1576 := derived1576 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1384 := derived1384 a h
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c1577 := derived1577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1579 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1537, some c78, some c58, some c63, some c353, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1579 : lratChecker f1579 p1579 = .success := by decide +kernel
theorem unsat1579 : Unsatisfiable (PosFin 57) f1579 := by
  apply lratCheckerSound f1579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1579
  · intro a ha; simp [p1579] at ha; subst a; trivial
  · exact checked1579
theorem derived1579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1579 := by
  apply localUnsat_implies_entails f1579 [c1489, c1537, c78, c58, c63, c353] c1579 unsat1579 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1537 := derived1537 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1580 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1576, some c1569, some c1538, some c1315, some c391, some c1222, some c303, some c143, some c5, some c183, some c193, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1580 : lratChecker f1580 p1580 = .success := by decide +kernel
theorem unsat1580 : Unsatisfiable (PosFin 57) f1580 := by
  apply lratCheckerSound f1580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1580
  · intro a ha; simp [p1580] at ha; subst a; trivial
  · exact checked1580
theorem derived1580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1580 := by
  apply localUnsat_implies_entails f1580 [c1578, c1576, c1569, c1538, c1315, c391, c1222, c303, c143, c5, c183, c193] c1580 unsat1580 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1576 := derived1576 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1538 := derived1538 a h
  have h4 : Entails.eval a c1315 := derived1315 a h
  have h5 : Entails.eval a c391 := h 390 (by decide)
  have h6 : Entails.eval a c1222 := derived1222 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1581 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c1211, some c110, some c1578, some c1576, some c104, some c1548, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1581 : lratChecker f1581 p1581 = .success := by decide +kernel
theorem unsat1581 : Unsatisfiable (PosFin 57) f1581 := by
  apply lratCheckerSound f1581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1581
  · intro a ha; simp [p1581] at ha; subst a; trivial
  · exact checked1581
theorem derived1581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1581 := by
  apply localUnsat_implies_entails f1581 [c1538, c1211, c110, c1578, c1576, c104, c1548] c1581 unsat1581 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1578 := derived1578 a h
  have h4 : Entails.eval a c1576 := derived1576 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c1548 := derived1548 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1582 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1576, some c1569, some c1538, some c1211, some c110, some c1581, some c389, some c1580, some c323, some c295, some c1215, some c73, some c53, some c8, some c279, some c342, some c193, some c72, some c1173, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1582 : lratChecker f1582 p1582 = .success := by decide +kernel
theorem unsat1582 : Unsatisfiable (PosFin 57) f1582 := by
  apply lratCheckerSound f1582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1582
  · intro a ha; simp [p1582] at ha; subst a; trivial
  · exact checked1582
theorem derived1582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1582 := by
  apply localUnsat_implies_entails f1582 [c1489, c1576, c1569, c1538, c1211, c110, c1581, c389, c1580, c323, c295, c1215, c73, c53, c8, c279, c342, c193, c72, c1173] c1582 unsat1582 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1576 := derived1576 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1538 := derived1538 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1581 := derived1581 a h
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c1580 := derived1580 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c72 := h 71 (by decide)
  have h19 : Entails.eval a c1173 := derived1173 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1583 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1576, some c1569, some c1538, some c323, some c321, some c1221, some c391, some c1222, some c1219, some c303, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1583 : lratChecker f1583 p1583 = .success := by decide +kernel
theorem unsat1583 : Unsatisfiable (PosFin 57) f1583 := by
  apply lratCheckerSound f1583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1583
  · intro a ha; simp [p1583] at ha; subst a; trivial
  · exact checked1583
theorem derived1583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1583 := by
  apply localUnsat_implies_entails f1583 [c1576, c1569, c1538, c323, c321, c1221, c391, c1222, c1219, c303] c1583 unsat1583 (by rfl) a
  have h0 : Entails.eval a c1576 := derived1576 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c323 := h 322 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c1221 := derived1221 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c1222 := derived1222 a h
  have h8 : Entails.eval a c1219 := derived1219 a h
  have h9 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1584 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1582, some c1583, some c41, some c1576, some c1569, some c1538, some c389, some c388, some c1222, some c303, some c1219, some c314, some c326, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1584 : lratChecker f1584 p1584 = .success := by decide +kernel
theorem unsat1584 : Unsatisfiable (PosFin 57) f1584 := by
  apply lratCheckerSound f1584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1584
  · intro a ha; simp [p1584] at ha; subst a; trivial
  · exact checked1584
theorem derived1584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1584 := by
  apply localUnsat_implies_entails f1584 [c1489, c1582, c1583, c41, c1576, c1569, c1538, c389, c388, c1222, c303, c1219, c314, c326] c1584 unsat1584 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1582 := derived1582 a h
  have h2 : Entails.eval a c1583 := derived1583 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c1576 := derived1576 a h
  have h5 : Entails.eval a c1569 := derived1569 a h
  have h6 : Entails.eval a c1538 := derived1538 a h
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c1222 := derived1222 a h
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c1219 := derived1219 a h
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1585 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c1569, some c1576, some c1582, some c1583, some c1584, some c74, some c1315, some c391, some c1222, some c303, some c143, some c177, some c183, some c193, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1585 : lratChecker f1585 p1585 = .success := by decide +kernel
theorem unsat1585 : Unsatisfiable (PosFin 57) f1585 := by
  apply lratCheckerSound f1585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1585
  · intro a ha; simp [p1585] at ha; subst a; trivial
  · exact checked1585
theorem derived1585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1585 := by
  apply localUnsat_implies_entails f1585 [c1538, c1569, c1576, c1582, c1583, c1584, c74, c1315, c391, c1222, c303, c143, c177, c183, c193] c1585 unsat1585 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1582 := derived1582 a h
  have h4 : Entails.eval a c1583 := derived1583 a h
  have h5 : Entails.eval a c1584 := derived1584 a h
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c1315 := derived1315 a h
  have h8 : Entails.eval a c391 := h 390 (by decide)
  have h9 : Entails.eval a c1222 := derived1222 a h
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c177 := h 176 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  have h14 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1586 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c78, some c307, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1586 : lratChecker f1586 p1586 = .success := by decide +kernel
theorem unsat1586 : Unsatisfiable (PosFin 57) f1586 := by
  apply lratCheckerSound f1586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1586
  · intro a ha; simp [p1586] at ha; subst a; trivial
  · exact checked1586
theorem derived1586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1586 := by
  apply localUnsat_implies_entails f1586 [c38, c78, c307] c1586 unsat1586 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1587 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1586, some c1287, some c385, some c343, some c342, some c1045, some c227, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1587 : lratChecker f1587 p1587 = .success := by decide +kernel
theorem unsat1587 : Unsatisfiable (PosFin 57) f1587 := by
  apply lratCheckerSound f1587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1587
  · intro a ha; simp [p1587] at ha; subst a; trivial
  · exact checked1587
theorem derived1587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1587 := by
  apply localUnsat_implies_entails f1587 [c1586, c1287, c385, c343, c342, c1045, c227] c1587 unsat1587 (by rfl) a
  have h0 : Entails.eval a c1586 := derived1586 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c1045 := derived1045 a h
  have h6 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1588 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨43, by decide⟩, false), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c336, some c301, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1588 : lratChecker f1588 p1588 = .success := by decide +kernel
theorem unsat1588 : Unsatisfiable (PosFin 57) f1588 := by
  apply lratCheckerSound f1588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1588
  · intro a ha; simp [p1588] at ha; subst a; trivial
  · exact checked1588
theorem derived1588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1588 := by
  apply localUnsat_implies_entails f1588 [c285, c336, c301] c1588 unsat1588 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1589 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c42, some c328, some c1221, some c145, some c37, some c1587, some c53, some c62, some c378, some c287, some c86, some c1588, some c144, some c36, some c12, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1589 : lratChecker f1589 p1589 = .success := by decide +kernel
theorem unsat1589 : Unsatisfiable (PosFin 57) f1589 := by
  apply lratCheckerSound f1589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1589
  · intro a ha; simp [p1589] at ha; subst a; trivial
  · exact checked1589
theorem derived1589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1589 := by
  apply localUnsat_implies_entails f1589 [c1489, c1585, c1287, c385, c42, c328, c1221, c145, c37, c1587, c53, c62, c378, c287, c86, c1588, c144, c36, c12] c1589 unsat1589 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c1587 := derived1587 a h
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c1588 := derived1588 a h
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1590 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c1589, some c1511, some c112, some c92, some c59, some c378, some c343, some c53, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1590 : lratChecker f1590 p1590 = .success := by decide +kernel
theorem unsat1590 : Unsatisfiable (PosFin 57) f1590 := by
  apply lratCheckerSound f1590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1590
  · intro a ha; simp [p1590] at ha; subst a; trivial
  · exact checked1590
theorem derived1590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1590 := by
  apply localUnsat_implies_entails f1590 [c1489, c1585, c1287, c385, c1589, c1511, c112, c92, c59, c378, c343, c53] c1590 unsat1590 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1589 := derived1589 a h
  have h5 : Entails.eval a c1511 := derived1511 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1591 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c392, some c385, some c94, some c95, some c108, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1591 : lratChecker f1591 p1591 = .success := by decide +kernel
theorem unsat1591 : Unsatisfiable (PosFin 57) f1591 := by
  apply lratCheckerSound f1591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1591
  · intro a ha; simp [p1591] at ha; subst a; trivial
  · exact checked1591
theorem derived1591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1591 := by
  apply localUnsat_implies_entails f1591 [c1489, c392, c385, c94, c95, c108] c1591 unsat1591 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c392 := h 391 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1592 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c109, some c1213, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1592 : lratChecker f1592 p1592 = .success := by decide +kernel
theorem unsat1592 : Unsatisfiable (PosFin 57) f1592 := by
  apply lratCheckerSound f1592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1592
  · intro a ha; simp [p1592] at ha; subst a; trivial
  · exact checked1592
theorem derived1592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1592 := by
  apply localUnsat_implies_entails f1592 [c110, c109, c1213] c1592 unsat1592 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c1213 := derived1213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived1592

end CochromaticTwenty.Certificates.B16_6_2
