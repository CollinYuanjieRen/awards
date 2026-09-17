import MerLeanExperiment.Certificates.B16_1_2.Steps1000_1099

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1494 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c1489, some c1453, some c1491, some c1492, some c204, some c11, some c1493, some c148, some c1444, some c201, some c1260, some c1412, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 57) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1432, c1481, c1489, c1453, c1491, c1492, c204, c11, c1493, c148, c1444, c201, c1260, c1412] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1453 := derived1453 a h
  have h4 : Entails.eval a c1491 := derived1491 a h
  have h5 : Entails.eval a c1492 := derived1492 a h
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c1493 := derived1493 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1444 := derived1444 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c1260 := derived1260 a h
  have h13 : Entails.eval a c1412 := derived1412 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c1273, some c1487, some c1260, some c5, some c1423, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 57) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c157, c1273, c1487, c1260, c5, c1423] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c1273 := derived1273 a h
  have h2 : Entails.eval a c1487 := derived1487 a h
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1423 := derived1423 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c1489, some c1494, some c202, some c1495, some c205, some c1492, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 57) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1432, c1481, c1489, c1494, c202, c1495, c205, c1492] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1494 := derived1494 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1495 := derived1495 a h
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c1492 := derived1492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c22, some c26, some c1461, some c201, some c1487, some c207, some c1486, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 57) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1432, c22, c26, c1461, c201, c1487, c207, c1486] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c1461 := derived1461 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c1487 := derived1487 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c1486 := derived1486 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1497, some c202, some c1470, some c205, some c1492, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 57) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1432, c1497, c202, c1470, c205, c1492] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1497 := derived1497 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1470 := derived1470 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c1492 := derived1492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1481, some c1496, some c1498, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 57) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1481, c1496, c1498] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1481 := derived1481 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c1498 := derived1498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨12, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c144, some c81, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 57) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c4, c144, c81] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c58, some c57, some c324, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 57) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1431, c58, c57, c324] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1449, some c146, some c1500, some c1501, some c1362, some c201, some c203, some c158, some c1448, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 57) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1432, c1449, c146, c1500, c1501, c1362, c201, c203, c158, c1448] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1449 := derived1449 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c1500 := derived1500 a h
  have h4 : Entails.eval a c1501 := derived1501 a h
  have h5 : Entails.eval a c1362 := derived1362 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c1448 := derived1448 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1449, some c1362, some c160, some c29, some c58, some c57, some c328, some c158, some c207, some c125, some c11, some c1387, some c226, some c309, some c200, some c254, some c105, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 57) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1432, c1431, c1449, c1362, c160, c29, c58, c57, c328, c158, c207, c125, c11, c1387, c226, c309, c200, c254, c105] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1449 := derived1449 a h
  have h3 : Entails.eval a c1362 := derived1362 a h
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c1387 := derived1387 a h
  have h14 : Entails.eval a c226 := h 225 (by decide)
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨39, by decide⟩, true), (⟨29, by decide⟩, false), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c29, some c58, some c127, some c328, some c215, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 57) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1431, c1432, c29, c58, c127, c328, c215] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1449, some c1499, some c1481, some c146, some c1502, some c1503, some c201, some c203, some c1260, some c158, some c1253, some c1451, some c83, some c10, some c2, some c171, some c82, some c1504, some c323, some c305, some c215, some c106, some c127, some c309, some c46, some c3, some c135, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 57) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c1432, c1431, c1449, c1499, c1481, c146, c1502, c1503, c201, c203, c1260, c158, c1253, c1451, c83, c10, c2, c171, c82, c1504, c323, c305, c215, c106, c127, c309, c46, c3, c135] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1449 := derived1449 a h
  have h3 : Entails.eval a c1499 := derived1499 a h
  have h4 : Entails.eval a c1481 := derived1481 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c1502 := derived1502 a h
  have h7 : Entails.eval a c1503 := derived1503 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c1260 := derived1260 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c1253 := derived1253 a h
  have h13 : Entails.eval a c1451 := derived1451 a h
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c171 := h 170 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  have h19 : Entails.eval a c1504 := derived1504 a h
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c305 := h 304 (by decide)
  have h22 : Entails.eval a c215 := h 214 (by decide)
  have h23 : Entails.eval a c106 := h 105 (by decide)
  have h24 : Entails.eval a c127 := h 126 (by decide)
  have h25 : Entails.eval a c309 := h 308 (by decide)
  have h26 : Entails.eval a c46 := h 45 (by decide)
  have h27 : Entails.eval a c3 := h 2 (by decide)
  have h28 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1486, some c305, some c58, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 57) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c1431, c1486, c305, c58] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1259, some c1481, some c1260, some c392, some c106, some c1506, some c145, some c82, some c353, some c168, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 57) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1431, c1259, c1481, c1260, c392, c106, c1506, c145, c82, c353, c168] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1259 := derived1259 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c392 := h 391 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c1506 := derived1506 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c45, some c232, some c126, some c362, some c214, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 57) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1431, c1432, c45, c232, c126, c362, c214] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c202, some c1449, some c10, some c2, some c1457, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 57) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1432, c202, c1449, c10, c2, c1457] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c1449 := derived1449 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1457 := derived1457 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1499, some c202, some c1507, some c1253, some c1449, some c1481, some c58, some c3, some c31, some c323, some c134, some c129, some c147, some c84, some c82, some c169, some c1508, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 57) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c1432, c1431, c1499, c202, c1507, c1253, c1449, c1481, c58, c3, c31, c323, c134, c129, c147, c84, c82, c169, c1508] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1499 := derived1499 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1507 := derived1507 a h
  have h5 : Entails.eval a c1253 := derived1253 a h
  have h6 : Entails.eval a c1449 := derived1449 a h
  have h7 : Entails.eval a c1481 := derived1481 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c1508 := derived1508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c126, some c125, some c226, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 57) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c1432, c126, c125, c226] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1505, some c202, some c1449, some c1499, some c1481, some c1507, some c1509, some c1510, some c1486, some c1511, some c37, some c29, some c46, some c45, some c174, some c173, some c323, some c131, some c250, some c228, some c276, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 57) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c1431, c1432, c1505, c202, c1449, c1499, c1481, c1507, c1509, c1510, c1486, c1511, c37, c29, c46, c45, c174, c173, c323, c131, c250, c228, c276] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1449 := derived1449 a h
  have h5 : Entails.eval a c1499 := derived1499 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c1507 := derived1507 a h
  have h8 : Entails.eval a c1509 := derived1509 a h
  have h9 : Entails.eval a c1510 := derived1510 a h
  have h10 : Entails.eval a c1486 := derived1486 a h
  have h11 : Entails.eval a c1511 := derived1511 a h
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c174 := h 173 (by decide)
  have h17 : Entails.eval a c173 := h 172 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c228 := h 227 (by decide)
  have h22 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c202, some c1259, some c316, some c305, some c1500, some c29, some c214, some c126, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 57) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c1431, c1432, c202, c1259, c316, c305, c1500, c29, c214, c126] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1259 := derived1259 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c1500 := derived1500 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c214 := h 213 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1505, some c202, some c1253, some c1449, some c1499, some c1481, some c1259, some c1512, some c201, some c1260, some c392, some c106, some c1513, some c145, some c82, some c353, some c144, some c169, some c1501, some c83, some c323, some c288, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 57) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c1432, c1431, c1505, c202, c1253, c1449, c1499, c1481, c1259, c1512, c201, c1260, c392, c106, c1513, c145, c82, c353, c144, c169, c1501, c83, c323, c288] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c1449 := derived1449 a h
  have h6 : Entails.eval a c1499 := derived1499 a h
  have h7 : Entails.eval a c1481 := derived1481 a h
  have h8 : Entails.eval a c1259 := derived1259 a h
  have h9 : Entails.eval a c1512 := derived1512 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c1260 := derived1260 a h
  have h12 : Entails.eval a c392 := h 391 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c1513 := derived1513 a h
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c1501 := derived1501 a h
  have h21 : Entails.eval a c83 := h 82 (by decide)
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c202, some c1253, some c1481, some c29, some c58, some c126, some c328, some c214, some c147, some c83, some c82, some c171, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 57) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c1431, c1432, c202, c1253, c1481, c29, c58, c126, c328, c214, c147, c83, c82, c171] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1253 := derived1253 a h
  have h4 : Entails.eval a c1481 := derived1481 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1253, some c84, some c82, some c171, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 57) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c1253, c84, c82, c171] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c1253 := derived1253 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c202, some c1481, some c1260, some c1516, some c147, some c323, some c29, some c58, some c1515, some c126, some c309, some c226, some c106, some c253, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 57) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1432, c1431, c202, c1481, c1260, c1516, c147, c323, c29, c58, c1515, c126, c309, c226, c106, c253] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1481 := derived1481 a h
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c1516 := derived1516 a h
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c1515 := derived1515 a h
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c3, some c309, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 57) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c11, c3, c309] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c127, some c135, some c46, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 57) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c1432, c1431, c127, c135, c46] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1499, some c1481, some c1449, some c1505, some c202, some c1514, some c205, some c10, some c2, some c1518, some c207, some c1260, some c1516, some c1517, some c1519, some c215, some c323, some c29, some c58, some c1504, some c126, some c309, some c226, some c106, some c253, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 57) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c1432, c1431, c1499, c1481, c1449, c1505, c202, c1514, c205, c10, c2, c1518, c207, c1260, c1516, c1517, c1519, c215, c323, c29, c58, c1504, c126, c309, c226, c106, c253] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1499 := derived1499 a h
  have h3 : Entails.eval a c1481 := derived1481 a h
  have h4 : Entails.eval a c1449 := derived1449 a h
  have h5 : Entails.eval a c1505 := derived1505 a h
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c1514 := derived1514 a h
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c1518 := derived1518 a h
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c1260 := derived1260 a h
  have h14 : Entails.eval a c1516 := derived1516 a h
  have h15 : Entails.eval a c1517 := derived1517 a h
  have h16 : Entails.eval a c1519 := derived1519 a h
  have h17 : Entails.eval a c215 := h 214 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c29 := h 28 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c1504 := derived1504 a h
  have h22 : Entails.eval a c126 := h 125 (by decide)
  have h23 : Entails.eval a c309 := h 308 (by decide)
  have h24 : Entails.eval a c226 := h 225 (by decide)
  have h25 : Entails.eval a c106 := h 105 (by decide)
  have h26 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1521 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c144, some c1500, some c80, some c170, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1521 : lratChecker f1521 p1521 = .success := by decide +kernel
theorem unsat1521 : Unsatisfiable (PosFin 57) f1521 := by
  apply lratCheckerSound f1521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1521
  · intro a ha; simp [p1521] at ha; subst a; trivial
  · exact checked1521
theorem derived1521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1521 := by
  apply localUnsat_implies_entails f1521 [c144, c1500, c80, c170] c1521 unsat1521 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c1500 := derived1500 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1522 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c10, some c542, some c1521, some c325, some c1501, some c1369, some c160, some c321, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1522 : lratChecker f1522 p1522 = .success := by decide +kernel
theorem unsat1522 : Unsatisfiable (PosFin 57) f1522 := by
  apply lratCheckerSound f1522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1522
  · intro a ha; simp [p1522] at ha; subst a; trivial
  · exact checked1522
theorem derived1522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1522 := by
  apply localUnsat_implies_entails f1522 [c2, c10, c542, c1521, c325, c1501, c1369, c160, c321] c1522 unsat1522 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c542 := derived542 a h
  have h3 : Entails.eval a c1521 := derived1521 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c1501 := derived1501 a h
  have h6 : Entails.eval a c1369 := derived1369 a h
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1523 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨37, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c29, some c58, some c125, some c1486, some c213, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1523 : lratChecker f1523 p1523 = .success := by decide +kernel
theorem unsat1523 : Unsatisfiable (PosFin 57) f1523 := by
  apply lratCheckerSound f1523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1523
  · intro a ha; simp [p1523] at ha; subst a; trivial
  · exact checked1523
theorem derived1523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1523 := by
  apply localUnsat_implies_entails f1523 [c1431, c1432, c29, c58, c125, c1486, c213] c1523 unsat1523 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c1486 := derived1486 a h
  have h6 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1524 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c542, some c1481, some c311, some c325, some c200, some c156, some c144, some c1500, some c80, some c172, some c1523, some c321, some c307, some c287, some c85, some c84, some c176, some c1254, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1524 : lratChecker f1524 p1524 = .success := by decide +kernel
theorem unsat1524 : Unsatisfiable (PosFin 57) f1524 := by
  apply lratCheckerSound f1524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1524
  · intro a ha; simp [p1524] at ha; subst a; trivial
  · exact checked1524
theorem derived1524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1524 := by
  apply localUnsat_implies_entails f1524 [c1431, c1432, c542, c1481, c311, c325, c200, c156, c144, c1500, c80, c172, c1523, c321, c307, c287, c85, c84, c176, c1254] c1524 unsat1524 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c542 := derived542 a h
  have h3 : Entails.eval a c1481 := derived1481 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c1500 := derived1500 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c1523 := derived1523 a h
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c85 := h 84 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c1254 := derived1254 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1525 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1481, some c1520, some c1493, some c10, some c2, some c1518, some c1499, some c542, some c1522, some c1524, some c146, some c160, some c1500, some c81, some c1501, some c324, some c168, some c321, some c31, some c82, some c213, some c134, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1525 : lratChecker f1525 p1525 = .success := by decide +kernel
theorem unsat1525 : Unsatisfiable (PosFin 57) f1525 := by
  apply lratCheckerSound f1525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1525
  · intro a ha; simp [p1525] at ha; subst a; trivial
  · exact checked1525
theorem derived1525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1525 := by
  apply localUnsat_implies_entails f1525 [c1481, c1520, c1493, c10, c2, c1518, c1499, c542, c1522, c1524, c146, c160, c1500, c81, c1501, c324, c168, c321, c31, c82, c213, c134] c1525 unsat1525 (by rfl) a
  have h0 : Entails.eval a c1481 := derived1481 a h
  have h1 : Entails.eval a c1520 := derived1520 a h
  have h2 : Entails.eval a c1493 := derived1493 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1518 := derived1518 a h
  have h6 : Entails.eval a c1499 := derived1499 a h
  have h7 : Entails.eval a c542 := derived542 a h
  have h8 : Entails.eval a c1522 := derived1522 a h
  have h9 : Entails.eval a c1524 := derived1524 a h
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c1500 := derived1500 a h
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c1501 := derived1501 a h
  have h15 : Entails.eval a c324 := h 323 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c321 := h 320 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c82 := h 81 (by decide)
  have h20 : Entails.eval a c213 := h 212 (by decide)
  have h21 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1526 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c200, some c198, some c386, some c393, some c106, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1526 : lratChecker f1526 p1526 = .success := by decide +kernel
theorem unsat1526 : Unsatisfiable (PosFin 57) f1526 := by
  apply lratCheckerSound f1526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1526
  · intro a ha; simp [p1526] at ha; subst a; trivial
  · exact checked1526
theorem derived1526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1526 := by
  apply localUnsat_implies_entails f1526 [c1431, c200, c198, c386, c393, c106] c1526 unsat1526 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c386 := h 385 (by decide)
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1527 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1520, some c1481, some c1493, some c10, some c2, some c1518, some c1525, some c207, some c1526, some c311, some c160, some c158, some c328, some c321, some c58, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1527 : lratChecker f1527 p1527 = .success := by decide +kernel
theorem unsat1527 : Unsatisfiable (PosFin 57) f1527 := by
  apply lratCheckerSound f1527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1527
  · intro a ha; simp [p1527] at ha; subst a; trivial
  · exact checked1527
theorem derived1527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1527 := by
  apply localUnsat_implies_entails f1527 [c1431, c1520, c1481, c1493, c10, c2, c1518, c1525, c207, c1526, c311, c160, c158, c328, c321, c58] c1527 unsat1527 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1520 := derived1520 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c1493 := derived1493 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1518 := derived1518 a h
  have h7 : Entails.eval a c1525 := derived1525 a h
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c1526 := derived1526 a h
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c321 := h 320 (by decide)
  have h15 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1528 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1520, some c1527, some c1253, some c148, some c1444, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1528 : lratChecker f1528 p1528 = .success := by decide +kernel
theorem unsat1528 : Unsatisfiable (PosFin 57) f1528 := by
  apply lratCheckerSound f1528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1528
  · intro a ha; simp [p1528] at ha; subst a; trivial
  · exact checked1528
theorem derived1528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1528 := by
  apply localUnsat_implies_entails f1528 [c1520, c1527, c1253, c148, c1444] c1528 unsat1528 (by rfl) a
  have h0 : Entails.eval a c1520 := derived1520 a h
  have h1 : Entails.eval a c1527 := derived1527 a h
  have h2 : Entails.eval a c1253 := derived1253 a h
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c1444 := derived1444 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1529 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c201, some c203, some c498, some c1260, some c1516, some c1424, some c1504, some c1519, some c321, some c215, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1529 : lratChecker f1529 p1529 = .success := by decide +kernel
theorem unsat1529 : Unsatisfiable (PosFin 57) f1529 := by
  apply lratCheckerSound f1529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1529
  · intro a ha; simp [p1529] at ha; subst a; trivial
  · exact checked1529
theorem derived1529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1529 := by
  apply localUnsat_implies_entails f1529 [c1432, c1481, c201, c203, c498, c1260, c1516, c1424, c1504, c1519, c321, c215] c1529 unsat1529 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c498 := derived498 a h
  have h5 : Entails.eval a c1260 := derived1260 a h
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c1424 := derived1424 a h
  have h8 : Entails.eval a c1504 := derived1504 a h
  have h9 : Entails.eval a c1519 := derived1519 a h
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1530 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c328, some c321, some c58, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1530 : lratChecker f1530 p1530 = .success := by decide +kernel
theorem unsat1530 : Unsatisfiable (PosFin 57) f1530 := by
  apply lratCheckerSound f1530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1530
  · intro a ha; simp [p1530] at ha; subst a; trivial
  · exact checked1530
theorem derived1530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1530 := by
  apply localUnsat_implies_entails f1530 [c1431, c328, c321, c58] c1530 unsat1530 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1531 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c31, some c129, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1531 : lratChecker f1531 p1531 = .success := by decide +kernel
theorem unsat1531 : Unsatisfiable (PosFin 57) f1531 := by
  apply lratCheckerSound f1531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1531
  · intro a ha; simp [p1531] at ha; subst a; trivial
  · exact checked1531
theorem derived1531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1531 := by
  apply localUnsat_implies_entails f1531 [c3, c31, c129] c1531 unsat1531 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1532 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨12, by decide⟩, true), (⟨31, by decide⟩, false), (⟨38, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c202, some c157, some c1501, some c1259, some c325, some c317, some c2, some c30, some c716, some c1531, some c1360, some c106, some c87, some c307, some c299, some c377, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1532 : lratChecker f1532 p1532 = .success := by decide +kernel
theorem unsat1532 : Unsatisfiable (PosFin 57) f1532 := by
  apply lratCheckerSound f1532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1532
  · intro a ha; simp [p1532] at ha; subst a; trivial
  · exact checked1532
theorem derived1532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1532 := by
  apply localUnsat_implies_entails f1532 [c1432, c1431, c202, c157, c1501, c1259, c325, c317, c2, c30, c716, c1531, c1360, c106, c87, c307, c299, c377] c1532 unsat1532 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c1501 := derived1501 a h
  have h5 : Entails.eval a c1259 := derived1259 a h
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c317 := h 316 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c716 := derived716 a h
  have h11 : Entails.eval a c1531 := derived1531 a h
  have h12 : Entails.eval a c1360 := derived1360 a h
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c307 := h 306 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1533 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c202, some c147, some c1530, some c159, some c168, some c1532, some c286, some c1511, some c80, some c46, some c45, some c47, some c272, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1533 : lratChecker f1533 p1533 = .success := by decide +kernel
theorem unsat1533 : Unsatisfiable (PosFin 57) f1533 := by
  apply lratCheckerSound f1533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1533
  · intro a ha; simp [p1533] at ha; subst a; trivial
  · exact checked1533
theorem derived1533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1533 := by
  apply localUnsat_implies_entails f1533 [c1432, c1431, c202, c147, c1530, c159, c168, c1532, c286, c1511, c80, c46, c45, c47, c272] c1533 unsat1533 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c1530 := derived1530 a h
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c1532 := derived1532 a h
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c1511 := derived1511 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1534 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1499, some c1481, some c1520, some c1529, some c1528, some c202, some c1253, some c148, some c84, some c83, some c147, some c1530, some c159, some c1533, some c205, some c207, some c10, some c2, some c1518, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1534 : lratChecker f1534 p1534 = .success := by decide +kernel
theorem unsat1534 : Unsatisfiable (PosFin 57) f1534 := by
  apply lratCheckerSound f1534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1534
  · intro a ha; simp [p1534] at ha; subst a; trivial
  · exact checked1534
theorem derived1534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1534 := by
  apply localUnsat_implies_entails f1534 [c1432, c1499, c1481, c1520, c1529, c1528, c202, c1253, c148, c84, c83, c147, c1530, c159, c1533, c205, c207, c10, c2, c1518] c1534 unsat1534 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1499 := derived1499 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c1520 := derived1520 a h
  have h4 : Entails.eval a c1529 := derived1529 a h
  have h5 : Entails.eval a c1528 := derived1528 a h
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c1253 := derived1253 a h
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c1530 := derived1530 a h
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c1533 := derived1533 a h
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c1518 := derived1518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1535 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c2, some c311, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1535 : lratChecker f1535 p1535 = .success := by decide +kernel
theorem unsat1535 : Unsatisfiable (PosFin 57) f1535 := by
  apply lratCheckerSound f1535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1535
  · intro a ha; simp [p1535] at ha; subst a; trivial
  · exact checked1535
theorem derived1535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1535 := by
  apply localUnsat_implies_entails f1535 [c10, c2, c311] c1535 unsat1535 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1536 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c14, some c6, some c1535, some c22, some c57, some c30, some c306, some c129, some c105, some c50, some c259, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1536 : lratChecker f1536 p1536 = .success := by decide +kernel
theorem unsat1536 : Unsatisfiable (PosFin 57) f1536 := by
  apply lratCheckerSound f1536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1536
  · intro a ha; simp [p1536] at ha; subst a; trivial
  · exact checked1536
theorem derived1536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1536 := by
  apply localUnsat_implies_entails f1536 [c1431, c14, c6, c1535, c22, c57, c30, c306, c129, c105, c50, c259] c1536 unsat1536 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c1535 := derived1535 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c129 := h 128 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1537 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c14, some c6, some c1535, some c1536, some c311, some c86, some c177, some c295, some c98, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1537 : lratChecker f1537 p1537 = .success := by decide +kernel
theorem unsat1537 : Unsatisfiable (PosFin 57) f1537 := by
  apply lratCheckerSound f1537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1537
  · intro a ha; simp [p1537] at ha; subst a; trivial
  · exact checked1537
theorem derived1537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1537 := by
  apply localUnsat_implies_entails f1537 [c22, c14, c6, c1535, c1536, c311, c86, c177, c295, c98] c1537 unsat1537 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c1535 := derived1535 a h
  have h4 : Entails.eval a c1536 := derived1536 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1538 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c985, some c34, some c37, some c45, some c174, some c131, some c90, some c10, some c259, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1538 : lratChecker f1538 p1538 = .success := by decide +kernel
theorem unsat1538 : Unsatisfiable (PosFin 57) f1538 := by
  apply lratCheckerSound f1538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1538
  · intro a ha; simp [p1538] at ha; subst a; trivial
  · exact checked1538
theorem derived1538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1538 := by
  apply localUnsat_implies_entails f1538 [c1431, c1432, c985, c34, c37, c45, c174, c131, c90, c10, c259] c1538 unsat1538 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c985 := derived985 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1539 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1537, some c1538, some c1449, some c202, some c205, some c1259, some c157, some c1080, some c317, some c86, some c1024, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1539 : lratChecker f1539 p1539 = .success := by decide +kernel
theorem unsat1539 : Unsatisfiable (PosFin 57) f1539 := by
  apply lratCheckerSound f1539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1539
  · intro a ha; simp [p1539] at ha; subst a; trivial
  · exact checked1539
theorem derived1539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1539 := by
  apply localUnsat_implies_entails f1539 [c1432, c1537, c1538, c1449, c202, c205, c1259, c157, c1080, c317, c86, c1024] c1539 unsat1539 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1537 := derived1537 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1449 := derived1449 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c1080 := derived1080 a h
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c1024 := derived1024 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1540 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c1499, some c1534, some c1537, some c202, some c1253, some c1538, some c1449, some c148, some c84, some c1539, some c10, some c2, some c1080, some c1518, some c1259, some c207, some c1529, some c147, some c159, some c1530, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1540 : lratChecker f1540 p1540 = .success := by decide +kernel
theorem unsat1540 : Unsatisfiable (PosFin 57) f1540 := by
  apply lratCheckerSound f1540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1540
  · intro a ha; simp [p1540] at ha; subst a; trivial
  · exact checked1540
theorem derived1540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1540 := by
  apply localUnsat_implies_entails f1540 [c1432, c1481, c1499, c1534, c1537, c202, c1253, c1538, c1449, c148, c84, c1539, c10, c2, c1080, c1518, c1259, c207, c1529, c147, c159, c1530] c1540 unsat1540 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1499 := derived1499 a h
  have h3 : Entails.eval a c1534 := derived1534 a h
  have h4 : Entails.eval a c1537 := derived1537 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1253 := derived1253 a h
  have h7 : Entails.eval a c1538 := derived1538 a h
  have h8 : Entails.eval a c1449 := derived1449 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c1539 := derived1539 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c1080 := derived1080 a h
  have h15 : Entails.eval a c1518 := derived1518 a h
  have h16 : Entails.eval a c1259 := derived1259 a h
  have h17 : Entails.eval a c207 := h 206 (by decide)
  have h18 : Entails.eval a c1529 := derived1529 a h
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c1530 := derived1530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1541 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1540, some c1481, some c122, some c121, some c1253, some c1254, some c1255, some c1085, some c1256, some c176, some c389, some c94, some c95, some c384, some c381, some c369, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1541 : lratChecker f1541 p1541 = .success := by decide +kernel
theorem unsat1541 : Unsatisfiable (PosFin 57) f1541 := by
  apply lratCheckerSound f1541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1541
  · intro a ha; simp [p1541] at ha; subst a; trivial
  · exact checked1541
theorem derived1541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1541 := by
  apply localUnsat_implies_entails f1541 [c1432, c1431, c1540, c1481, c122, c121, c1253, c1254, c1255, c1085, c1256, c176, c389, c94, c95, c384, c381, c369] c1541 unsat1541 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1540 := derived1540 a h
  have h3 : Entails.eval a c1481 := derived1481 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c1253 := derived1253 a h
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c1255 := derived1255 a h
  have h9 : Entails.eval a c1085 := derived1085 a h
  have h10 : Entails.eval a c1256 := derived1256 a h
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c384 := h 383 (by decide)
  have h16 : Entails.eval a c381 := h 380 (by decide)
  have h17 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1542 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c14, some c82, some c172, some c168, some c354, some c80, some c12, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1542 : lratChecker f1542 p1542 = .success := by decide +kernel
theorem unsat1542 : Unsatisfiable (PosFin 57) f1542 := by
  apply lratCheckerSound f1542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1542
  · intro a ha; simp [p1542] at ha; subst a; trivial
  · exact checked1542
theorem derived1542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1542 := by
  apply localUnsat_implies_entails f1542 [c1541, c14, c82, c172, c168, c354, c80, c12] c1542 unsat1542 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1543 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1481, some c58, some c29, some c1486, some c1435, some c1542, some c145, some c1523, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1543 : lratChecker f1543 p1543 = .success := by decide +kernel
theorem unsat1543 : Unsatisfiable (PosFin 57) f1543 := by
  apply lratCheckerSound f1543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1543
  · intro a ha; simp [p1543] at ha; subst a; trivial
  · exact checked1543
theorem derived1543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1543 := by
  apply localUnsat_implies_entails f1543 [c1431, c1481, c58, c29, c1486, c1435, c1542, c145, c1523] c1543 unsat1543 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c1486 := derived1486 a h
  have h5 : Entails.eval a c1435 := derived1435 a h
  have h6 : Entails.eval a c1542 := derived1542 a h
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c1523 := derived1523 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1544 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c6, some c1481, some c22, some c1362, some c326, some c1543, some c204, some c207, some c153, some c152, some c1530, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1544 : lratChecker f1544 p1544 = .success := by decide +kernel
theorem unsat1544 : Unsatisfiable (PosFin 57) f1544 := by
  apply lratCheckerSound f1544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1544
  · intro a ha; simp [p1544] at ha; subst a; trivial
  · exact checked1544
theorem derived1544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1544 := by
  apply localUnsat_implies_entails f1544 [c1541, c6, c1481, c22, c1362, c326, c1543, c204, c207, c153, c152, c1530] c1544 unsat1544 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1362 := derived1362 a h
  have h5 : Entails.eval a c326 := h 325 (by decide)
  have h6 : Entails.eval a c1543 := derived1543 a h
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c1530 := derived1530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1545 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨42, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c289, some c31, some c1531, some c1263, some c262, some c244, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1545 : lratChecker f1545 p1545 = .success := by decide +kernel
theorem unsat1545 : Unsatisfiable (PosFin 57) f1545 := by
  apply lratCheckerSound f1545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1545
  · intro a ha; simp [p1545] at ha; subst a; trivial
  · exact checked1545
theorem derived1545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1545 := by
  apply localUnsat_implies_entails f1545 [c1486, c289, c31, c1531, c1263, c262, c244] c1545 unsat1545 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c1531 := derived1531 a h
  have h4 : Entails.eval a c1263 := derived1263 a h
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1546 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c26, some c145, some c1542, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1546 : lratChecker f1546 p1546 = .success := by decide +kernel
theorem unsat1546 : Unsatisfiable (PosFin 57) f1546 := by
  apply lratCheckerSound f1546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1546
  · intro a ha; simp [p1546] at ha; subst a; trivial
  · exact checked1546
theorem derived1546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1546 := by
  apply localUnsat_implies_entails f1546 [c1541, c26, c145, c1542] c1546 unsat1546 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c1542 := derived1542 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1547 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c203, some c1541, some c6, some c14, some c1481, some c22, some c204, some c1543, some c306, some c85, some c106, some c176, some c290, some c98, some c177, some c1545, some c1546, some c182, some c1263, some c392, some c393, some c196, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1547 : lratChecker f1547 p1547 = .success := by decide +kernel
theorem unsat1547 : Unsatisfiable (PosFin 57) f1547 := by
  apply lratCheckerSound f1547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1547
  · intro a ha; simp [p1547] at ha; subst a; trivial
  · exact checked1547
theorem derived1547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1547 := by
  apply localUnsat_implies_entails f1547 [c1431, c1432, c203, c1541, c6, c14, c1481, c22, c204, c1543, c306, c85, c106, c176, c290, c98, c177, c1545, c1546, c182, c1263, c392, c393, c196] c1547 unsat1547 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c1541 := derived1541 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c1543 := derived1543 a h
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c176 := h 175 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c177 := h 176 (by decide)
  have h17 : Entails.eval a c1545 := derived1545 a h
  have h18 : Entails.eval a c1546 := derived1546 a h
  have h19 : Entails.eval a c182 := h 181 (by decide)
  have h20 : Entails.eval a c1263 := derived1263 a h
  have h21 : Entails.eval a c392 := h 391 (by decide)
  have h22 : Entails.eval a c393 := h 392 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1548 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c1481, some c1530, some c153, some c156, some c1317, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1548 : lratChecker f1548 p1548 = .success := by decide +kernel
theorem unsat1548 : Unsatisfiable (PosFin 57) f1548 := by
  apply lratCheckerSound f1548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1548
  · intro a ha; simp [p1548] at ha; subst a; trivial
  · exact checked1548
theorem derived1548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1548 := by
  apply localUnsat_implies_entails f1548 [c1541, c1481, c1530, c153, c156, c1317] c1548 unsat1548 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1530 := derived1530 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c1317 := derived1317 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1549 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1547, some c203, some c1541, some c6, some c14, some c1481, some c22, some c1543, some c306, some c85, some c106, some c176, some c290, some c98, some c1548, some c1546, some c182, some c1263, some c392, some c393, some c196, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1549 : lratChecker f1549 p1549 = .success := by decide +kernel
theorem unsat1549 : Unsatisfiable (PosFin 57) f1549 := by
  apply lratCheckerSound f1549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1549
  · intro a ha; simp [p1549] at ha; subst a; trivial
  · exact checked1549
theorem derived1549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1549 := by
  apply localUnsat_implies_entails f1549 [c1431, c1432, c1547, c203, c1541, c6, c14, c1481, c22, c1543, c306, c85, c106, c176, c290, c98, c1548, c1546, c182, c1263, c392, c393, c196] c1549 unsat1549 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1547 := derived1547 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c1541 := derived1541 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c1481 := derived1481 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c1543 := derived1543 a h
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c176 := h 175 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c1548 := derived1548 a h
  have h17 : Entails.eval a c1546 := derived1546 a h
  have h18 : Entails.eval a c182 := h 181 (by decide)
  have h19 : Entails.eval a c1263 := derived1263 a h
  have h20 : Entails.eval a c392 := h 391 (by decide)
  have h21 : Entails.eval a c393 := h 392 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1550 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1541, some c1481, some c22, some c1549, some c207, some c26, some c1547, some c203, some c1544, some c1530, some c147, some c153, some c82, some c1317, some c164, some c170, some c363, some c362, some c285, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1550 : lratChecker f1550 p1550 = .success := by decide +kernel
theorem unsat1550 : Unsatisfiable (PosFin 57) f1550 := by
  apply lratCheckerSound f1550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1550
  · intro a ha; simp [p1550] at ha; subst a; trivial
  · exact checked1550
theorem derived1550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1550 := by
  apply localUnsat_implies_entails f1550 [c1432, c1541, c1481, c22, c1549, c207, c26, c1547, c203, c1544, c1530, c147, c153, c82, c1317, c164, c170, c363, c362, c285] c1550 unsat1550 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1541 := derived1541 a h
  have h2 : Entails.eval a c1481 := derived1481 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1549 := derived1549 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1547 := derived1547 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c1544 := derived1544 a h
  have h10 : Entails.eval a c1530 := derived1530 a h
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c153 := h 152 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c1317 := derived1317 a h
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c362 := h 361 (by decide)
  have h19 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1551 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c1541, some c22, some c203, some c1544, some c1547, some c1549, some c207, some c26, some c1550, some c1369, some c145, some c82, some c172, some c165, some c363, some c362, some c285, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1551 : lratChecker f1551 p1551 = .success := by decide +kernel
theorem unsat1551 : Unsatisfiable (PosFin 57) f1551 := by
  apply lratCheckerSound f1551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1551
  · intro a ha; simp [p1551] at ha; subst a; trivial
  · exact checked1551
theorem derived1551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1551 := by
  apply localUnsat_implies_entails f1551 [c1432, c1481, c1541, c22, c203, c1544, c1547, c1549, c207, c26, c1550, c1369, c145, c82, c172, c165, c363, c362, c285] c1551 unsat1551 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1541 := derived1541 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c1544 := derived1544 a h
  have h6 : Entails.eval a c1547 := derived1547 a h
  have h7 : Entails.eval a c1549 := derived1549 a h
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1550 := derived1550 a h
  have h11 : Entails.eval a c1369 := derived1369 a h
  have h12 : Entails.eval a c145 := h 144 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1552 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1551, some c1541, some c6, some c14, some c1259, some c317, some c157, some c4, some c144, some c1544, some c354, some c201, some c170, some c26, some c80, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1552 : lratChecker f1552 p1552 = .success := by decide +kernel
theorem unsat1552 : Unsatisfiable (PosFin 57) f1552 := by
  apply lratCheckerSound f1552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1552
  · intro a ha; simp [p1552] at ha; subst a; trivial
  · exact checked1552
theorem derived1552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1552 := by
  apply localUnsat_implies_entails f1552 [c1432, c1551, c1541, c6, c14, c1259, c317, c157, c4, c144, c1544, c354, c201, c170, c26, c80] c1552 unsat1552 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1551 := derived1551 a h
  have h2 : Entails.eval a c1541 := derived1541 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c1259 := derived1259 a h
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c1544 := derived1544 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1553 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c1481, some c22, some c1552, some c207, some c26, some c1551, some c1516, some c1544, some c147, some c159, some c1530, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1553 : lratChecker f1553 p1553 = .success := by decide +kernel
theorem unsat1553 : Unsatisfiable (PosFin 57) f1553 := by
  apply lratCheckerSound f1553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1553
  · intro a ha; simp [p1553] at ha; subst a; trivial
  · exact checked1553
theorem derived1553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1553 := by
  apply localUnsat_implies_entails f1553 [c1541, c1481, c22, c1552, c207, c26, c1551, c1516, c1544, c147, c159, c1530] c1553 unsat1553 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1552 := derived1552 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c1551 := derived1551 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c1544 := derived1544 a h
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c1530 := derived1530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1554 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1541, some c1481, some c22, some c6, some c1551, some c1552, some c204, some c207, some c26, some c1516, some c1553, some c1529, some c322, some c326, some c1504, some c152, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1554 : lratChecker f1554 p1554 = .success := by decide +kernel
theorem unsat1554 : Unsatisfiable (PosFin 57) f1554 := by
  apply lratCheckerSound f1554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1554
  · intro a ha; simp [p1554] at ha; subst a; trivial
  · exact checked1554
theorem derived1554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1554 := by
  apply localUnsat_implies_entails f1554 [c1541, c1481, c22, c6, c1551, c1552, c204, c207, c26, c1516, c1553, c1529, c322, c326, c1504, c152] c1554 unsat1554 (by rfl) a
  have h0 : Entails.eval a c1541 := derived1541 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1551 := derived1551 a h
  have h5 : Entails.eval a c1552 := derived1552 a h
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c1553 := derived1553 a h
  have h11 : Entails.eval a c1529 := derived1529 a h
  have h12 : Entails.eval a c322 := h 321 (by decide)
  have h13 : Entails.eval a c326 := h 325 (by decide)
  have h14 : Entails.eval a c1504 := derived1504 a h
  have h15 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1555 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1260, some c1541, some c1481, some c1259, some c1507, some c392, some c5, some c840, some c106, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1555 : lratChecker f1555 p1555 = .success := by decide +kernel
theorem unsat1555 : Unsatisfiable (PosFin 57) f1555 := by
  apply lratCheckerSound f1555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1555
  · intro a ha; simp [p1555] at ha; subst a; trivial
  · exact checked1555
theorem derived1555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1555 := by
  apply localUnsat_implies_entails f1555 [c1432, c1431, c1554, c202, c1260, c1541, c1481, c1259, c1507, c392, c5, c840, c106] c1555 unsat1555 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c1541 := derived1541 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c1259 := derived1259 a h
  have h8 : Entails.eval a c1507 := derived1507 a h
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c840 := derived840 a h
  have h12 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1556 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1260, some c1541, some c1481, some c1530, some c147, some c1516, some c841, some c840, some c102, some c85, some c1003, some c289, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1556 : lratChecker f1556 p1556 = .success := by decide +kernel
theorem unsat1556 : Unsatisfiable (PosFin 57) f1556 := by
  apply lratCheckerSound f1556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1556
  · intro a ha; simp [p1556] at ha; subst a; trivial
  · exact checked1556
theorem derived1556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1556 := by
  apply localUnsat_implies_entails f1556 [c1432, c1431, c1554, c202, c1260, c1541, c1481, c1530, c147, c1516, c841, c840, c102, c85, c1003, c289] c1556 unsat1556 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c1541 := derived1541 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c1530 := derived1530 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c840 := derived840 a h
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c1003 := derived1003 a h
  have h15 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1557 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1541, some c1555, some c205, some c1556, some c159, some c152, some c5, some c326, some c1516, some c985, some c147, some c29, some c323, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1557 : lratChecker f1557 p1557 = .success := by decide +kernel
theorem unsat1557 : Unsatisfiable (PosFin 57) f1557 := by
  apply lratCheckerSound f1557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1557
  · intro a ha; simp [p1557] at ha; subst a; trivial
  · exact checked1557
theorem derived1557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1557 := by
  apply localUnsat_implies_entails f1557 [c1432, c1431, c1554, c202, c1541, c1555, c205, c1556, c159, c152, c5, c326, c1516, c985, c147, c29, c323] c1557 unsat1557 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1541 := derived1541 a h
  have h5 : Entails.eval a c1555 := derived1555 a h
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c1556 := derived1556 a h
  have h8 : Entails.eval a c159 := h 158 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c1516 := derived1516 a h
  have h13 : Entails.eval a c985 := derived985 a h
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1558 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c205, some c202, some c1253, some c1541, some c1540, some c1481, some c58, some c62, some c1531, some c1015, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1558 : lratChecker f1558 p1558 = .success := by decide +kernel
theorem unsat1558 : Unsatisfiable (PosFin 57) f1558 := by
  apply lratCheckerSound f1558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1558
  · intro a ha; simp [p1558] at ha; subst a; trivial
  · exact checked1558
theorem derived1558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1558 := by
  apply localUnsat_implies_entails f1558 [c1432, c1431, c1554, c205, c202, c1253, c1541, c1540, c1481, c58, c62, c1531, c1015] c1558 unsat1558 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1253 := derived1253 a h
  have h6 : Entails.eval a c1541 := derived1541 a h
  have h7 : Entails.eval a c1540 := derived1540 a h
  have h8 : Entails.eval a c1481 := derived1481 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c1531 := derived1531 a h
  have h12 : Entails.eval a c1015 := derived1015 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1559 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1554, some c205, some c1558, some c1486, some c202, some c1259, some c1541, some c1479, some c66, some c317, some c157, some c1488, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1559 : lratChecker f1559 p1559 = .success := by decide +kernel
theorem unsat1559 : Unsatisfiable (PosFin 57) f1559 := by
  apply lratCheckerSound f1559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1559
  · intro a ha; simp [p1559] at ha; subst a; trivial
  · exact checked1559
theorem derived1559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1559 := by
  apply localUnsat_implies_entails f1559 [c1432, c1554, c205, c1558, c1486, c202, c1259, c1541, c1479, c66, c317, c157, c1488] c1559 unsat1559 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1554 := derived1554 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c1558 := derived1558 a h
  have h4 : Entails.eval a c1486 := derived1486 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c1541 := derived1541 a h
  have h8 : Entails.eval a c1479 := derived1479 a h
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c1488 := derived1488 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1560 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1559, some c1554, some c202, some c205, some c1259, some c1557, some c1541, some c1481, some c322, some c29, some c1523, some c126, some c82, some c42, some c168, some c303, some c174, some c353, some c80, some c94, some c95, some c1263, some c384, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1560 : lratChecker f1560 p1560 = .success := by decide +kernel
theorem unsat1560 : Unsatisfiable (PosFin 57) f1560 := by
  apply lratCheckerSound f1560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1560
  · intro a ha; simp [p1560] at ha; subst a; trivial
  · exact checked1560
theorem derived1560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1560 := by
  apply localUnsat_implies_entails f1560 [c1432, c1431, c1559, c1554, c202, c205, c1259, c1557, c1541, c1481, c322, c29, c1523, c126, c82, c42, c168, c303, c174, c353, c80, c94, c95, c1263, c384] c1560 unsat1560 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1559 := derived1559 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c1557 := derived1557 a h
  have h8 : Entails.eval a c1541 := derived1541 a h
  have h9 : Entails.eval a c1481 := derived1481 a h
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c1523 := derived1523 a h
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c82 := h 81 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c353 := h 352 (by decide)
  have h20 : Entails.eval a c80 := h 79 (by decide)
  have h21 : Entails.eval a c94 := h 93 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  have h23 : Entails.eval a c1263 := derived1263 a h
  have h24 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1561 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1559, some c1554, some c205, some c1558, some c1486, some c202, some c1259, some c1557, some c1541, some c1481, some c1560, some c985, some c37, some c29, some c292, some c173, some c323, some c1263, some c633, some c392, some c11, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1561 : lratChecker f1561 p1561 = .success := by decide +kernel
theorem unsat1561 : Unsatisfiable (PosFin 57) f1561 := by
  apply lratCheckerSound f1561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1561
  · intro a ha; simp [p1561] at ha; subst a; trivial
  · exact checked1561
theorem derived1561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1561 := by
  apply localUnsat_implies_entails f1561 [c1431, c1432, c1559, c1554, c205, c1558, c1486, c202, c1259, c1557, c1541, c1481, c1560, c985, c37, c29, c292, c173, c323, c1263, c633, c392, c11] c1561 unsat1561 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1559 := derived1559 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c1558 := derived1558 a h
  have h6 : Entails.eval a c1486 := derived1486 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1259 := derived1259 a h
  have h9 : Entails.eval a c1557 := derived1557 a h
  have h10 : Entails.eval a c1541 := derived1541 a h
  have h11 : Entails.eval a c1481 := derived1481 a h
  have h12 : Entails.eval a c1560 := derived1560 a h
  have h13 : Entails.eval a c985 := derived985 a h
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c173 := h 172 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c1263 := derived1263 a h
  have h20 : Entails.eval a c633 := derived633 a h
  have h21 : Entails.eval a c392 := h 391 (by decide)
  have h22 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1562 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1554, some c202, some c1253, some c1541, some c1540, some c1481, some c205, some c1558, some c1486, some c1559, some c1561, some c148, some c157, some c1360, some c84, some c76, some c324, some c110, some c168, some c280, some c1480, some c80, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1562 : lratChecker f1562 p1562 = .success := by decide +kernel
theorem unsat1562 : Unsatisfiable (PosFin 57) f1562 := by
  apply lratCheckerSound f1562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1562
  · intro a ha; simp [p1562] at ha; subst a; trivial
  · exact checked1562
theorem derived1562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1562 := by
  apply localUnsat_implies_entails f1562 [c1432, c1554, c202, c1253, c1541, c1540, c1481, c205, c1558, c1486, c1559, c1561, c148, c157, c1360, c84, c76, c324, c110, c168, c280, c1480, c80] c1562 unsat1562 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1554 := derived1554 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1253 := derived1253 a h
  have h4 : Entails.eval a c1541 := derived1541 a h
  have h5 : Entails.eval a c1540 := derived1540 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c1558 := derived1558 a h
  have h9 : Entails.eval a c1486 := derived1486 a h
  have h10 : Entails.eval a c1559 := derived1559 a h
  have h11 : Entails.eval a c1561 := derived1561 a h
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c1360 := derived1360 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c324 := h 323 (by decide)
  have h18 : Entails.eval a c110 := h 109 (by decide)
  have h19 : Entails.eval a c168 := h 167 (by decide)
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c1480 := derived1480 a h
  have h22 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1563 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1562, some c1557, some c1554, some c202, some c1253, some c1481, some c1530, some c1548, some c147, some c153, some c207, some c84, some c11, some c1518, some c167, some c193, some c352, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1563 : lratChecker f1563 p1563 = .success := by decide +kernel
theorem unsat1563 : Unsatisfiable (PosFin 57) f1563 := by
  apply lratCheckerSound f1563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1563
  · intro a ha; simp [p1563] at ha; subst a; trivial
  · exact checked1563
theorem derived1563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1563 := by
  apply localUnsat_implies_entails f1563 [c1432, c1562, c1557, c1554, c202, c1253, c1481, c1530, c1548, c147, c153, c207, c84, c11, c1518, c167, c193, c352] c1563 unsat1563 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1562 := derived1562 a h
  have h2 : Entails.eval a c1557 := derived1557 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1253 := derived1253 a h
  have h6 : Entails.eval a c1481 := derived1481 a h
  have h7 : Entails.eval a c1530 := derived1530 a h
  have h8 : Entails.eval a c1548 := derived1548 a h
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c1518 := derived1518 a h
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1564 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1554, some c202, some c1259, some c1563, some c1557, some c1541, some c1481, some c1487, some c1479, some c66, some c317, some c157, some c1488, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1564 : lratChecker f1564 p1564 = .success := by decide +kernel
theorem unsat1564 : Unsatisfiable (PosFin 57) f1564 := by
  apply lratCheckerSound f1564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1564
  · intro a ha; simp [p1564] at ha; subst a; trivial
  · exact checked1564
theorem derived1564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1564 := by
  apply localUnsat_implies_entails f1564 [c1432, c1554, c202, c1259, c1563, c1557, c1541, c1481, c1487, c1479, c66, c317, c157, c1488] c1564 unsat1564 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1554 := derived1554 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1259 := derived1259 a h
  have h4 : Entails.eval a c1563 := derived1563 a h
  have h5 : Entails.eval a c1557 := derived1557 a h
  have h6 : Entails.eval a c1541 := derived1541 a h
  have h7 : Entails.eval a c1481 := derived1481 a h
  have h8 : Entails.eval a c1487 := derived1487 a h
  have h9 : Entails.eval a c1479 := derived1479 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c1488 := derived1488 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1565 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1564, some c1562, some c1481, some c1541, some c1554, some c202, some c1259, some c1080, some c193, some c1557, some c1253, some c1540, some c326, some c322, some c142, some c153, some c29, some c58, some c1003, some c1523, some c76, some c315, some c126, some c255, some c82, some c169, some c110, some c240, some c354, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1565 : lratChecker f1565 p1565 = .success := by decide +kernel
theorem unsat1565 : Unsatisfiable (PosFin 57) f1565 := by
  apply lratCheckerSound f1565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1565
  · intro a ha; simp [p1565] at ha; subst a; trivial
  · exact checked1565
theorem derived1565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1565 := by
  apply localUnsat_implies_entails f1565 [c1431, c1432, c1564, c1562, c1481, c1541, c1554, c202, c1259, c1080, c193, c1557, c1253, c1540, c326, c322, c142, c153, c29, c58, c1003, c1523, c76, c315, c126, c255, c82, c169, c110, c240, c354] c1565 unsat1565 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1562 := derived1562 a h
  have h4 : Entails.eval a c1481 := derived1481 a h
  have h5 : Entails.eval a c1541 := derived1541 a h
  have h6 : Entails.eval a c1554 := derived1554 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1259 := derived1259 a h
  have h9 : Entails.eval a c1080 := derived1080 a h
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c1557 := derived1557 a h
  have h12 : Entails.eval a c1253 := derived1253 a h
  have h13 : Entails.eval a c1540 := derived1540 a h
  have h14 : Entails.eval a c326 := h 325 (by decide)
  have h15 : Entails.eval a c322 := h 321 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c153 := h 152 (by decide)
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c58 := h 57 (by decide)
  have h20 : Entails.eval a c1003 := derived1003 a h
  have h21 : Entails.eval a c1523 := derived1523 a h
  have h22 : Entails.eval a c76 := h 75 (by decide)
  have h23 : Entails.eval a c315 := h 314 (by decide)
  have h24 : Entails.eval a c126 := h 125 (by decide)
  have h25 : Entails.eval a c255 := h 254 (by decide)
  have h26 : Entails.eval a c82 := h 81 (by decide)
  have h27 : Entails.eval a c169 := h 168 (by decide)
  have h28 : Entails.eval a c110 := h 109 (by decide)
  have h29 : Entails.eval a c240 := h 239 (by decide)
  have h30 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1566 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1562, some c1541, some c1481, some c1565, some c985, some c62, some c29, some c323, some c153, some c156, some c324, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1566 : lratChecker f1566 p1566 = .success := by decide +kernel
theorem unsat1566 : Unsatisfiable (PosFin 57) f1566 := by
  apply lratCheckerSound f1566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1566
  · intro a ha; simp [p1566] at ha; subst a; trivial
  · exact checked1566
theorem derived1566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1566 := by
  apply localUnsat_implies_entails f1566 [c1432, c1431, c1562, c1541, c1481, c1565, c985, c62, c29, c323, c153, c156, c324] c1566 unsat1566 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1562 := derived1562 a h
  have h3 : Entails.eval a c1541 := derived1541 a h
  have h4 : Entails.eval a c1481 := derived1481 a h
  have h5 : Entails.eval a c1565 := derived1565 a h
  have h6 : Entails.eval a c985 := derived985 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1567 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1562, some c1554, some c202, some c1253, some c1540, some c84, some c76, some c165, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1567 : lratChecker f1567 p1567 = .success := by decide +kernel
theorem unsat1567 : Unsatisfiable (PosFin 57) f1567 := by
  apply lratCheckerSound f1567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1567
  · intro a ha; simp [p1567] at ha; subst a; trivial
  · exact checked1567
theorem derived1567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1567 := by
  apply localUnsat_implies_entails f1567 [c1432, c1562, c1554, c202, c1253, c1540, c84, c76, c165] c1567 unsat1567 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1562 := derived1562 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c1540 := derived1540 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1568 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨35, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c142, some c153, some c346, some c1387, some c193, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1568 : lratChecker f1568 p1568 = .success := by decide +kernel
theorem unsat1568 : Unsatisfiable (PosFin 57) f1568 := by
  apply lratCheckerSound f1568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1568
  · intro a ha; simp [p1568] at ha; subst a; trivial
  · exact checked1568
theorem derived1568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1568 := by
  apply localUnsat_implies_entails f1568 [c11, c142, c153, c346, c1387, c193] c1568 unsat1568 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c1387 := derived1387 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1569 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1541, some c1481, some c1557, some c1562, some c1567, some c148, some c1566, some c207, some c11, some c3, some c167, some c1568, some c324, some c326, some c1518, some c985, some c34, some c193, some c46, some c137, some c1387, some c263, some c224, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1569 : lratChecker f1569 p1569 = .success := by decide +kernel
theorem unsat1569 : Unsatisfiable (PosFin 57) f1569 := by
  apply lratCheckerSound f1569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1569
  · intro a ha; simp [p1569] at ha; subst a; trivial
  · exact checked1569
theorem derived1569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1569 := by
  apply localUnsat_implies_entails f1569 [c1432, c1431, c1554, c202, c1541, c1481, c1557, c1562, c1567, c148, c1566, c207, c11, c3, c167, c1568, c324, c326, c1518, c985, c34, c193, c46, c137, c1387, c263, c224] c1569 unsat1569 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1541 := derived1541 a h
  have h5 : Entails.eval a c1481 := derived1481 a h
  have h6 : Entails.eval a c1557 := derived1557 a h
  have h7 : Entails.eval a c1562 := derived1562 a h
  have h8 : Entails.eval a c1567 := derived1567 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1566 := derived1566 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c1568 := derived1568 a h
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c326 := h 325 (by decide)
  have h18 : Entails.eval a c1518 := derived1518 a h
  have h19 : Entails.eval a c985 := derived985 a h
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  have h22 : Entails.eval a c46 := h 45 (by decide)
  have h23 : Entails.eval a c137 := h 136 (by decide)
  have h24 : Entails.eval a c1387 := derived1387 a h
  have h25 : Entails.eval a c263 := h 262 (by decide)
  have h26 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1570 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1569, some c201, some c1260, some c1541, some c1481, some c205, some c1259, some c1080, some c392, some c106, some c87, some c11, some c386, some c183, some c177, some c370, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1570 : lratChecker f1570 p1570 = .success := by decide +kernel
theorem unsat1570 : Unsatisfiable (PosFin 57) f1570 := by
  apply lratCheckerSound f1570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1570
  · intro a ha; simp [p1570] at ha; subst a; trivial
  · exact checked1570
theorem derived1570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1570 := by
  apply localUnsat_implies_entails f1570 [c1432, c1431, c1554, c202, c1569, c201, c1260, c1541, c1481, c205, c1259, c1080, c392, c106, c87, c11, c386, c183, c177, c370] c1570 unsat1570 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1569 := derived1569 a h
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c1260 := derived1260 a h
  have h7 : Entails.eval a c1541 := derived1541 a h
  have h8 : Entails.eval a c1481 := derived1481 a h
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c1259 := derived1259 a h
  have h11 : Entails.eval a c1080 := derived1080 a h
  have h12 : Entails.eval a c392 := h 391 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c386 := h 385 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  have h18 : Entails.eval a c177 := h 176 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1571 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1570, some c1554, some c202, some c1569, some c201, some c1260, some c1541, some c1481, some c1080, some c392, some c106, some c87, some c11, some c110, some c386, some c183, some c1519, some c370, some c381, some c248, some c264, some c265, some c54, some c34, some c1516, some c1529, some c326, some c322, some c152, some c1504, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1571 : lratChecker f1571 p1571 = .success := by decide +kernel
theorem unsat1571 : Unsatisfiable (PosFin 57) f1571 := by
  apply lratCheckerSound f1571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1571
  · intro a ha; simp [p1571] at ha; subst a; trivial
  · exact checked1571
theorem derived1571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1571 := by
  apply localUnsat_implies_entails f1571 [c1432, c1431, c1570, c1554, c202, c1569, c201, c1260, c1541, c1481, c1080, c392, c106, c87, c11, c110, c386, c183, c1519, c370, c381, c248, c264, c265, c54, c34, c1516, c1529, c326, c322, c152, c1504] c1571 unsat1571 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1570 := derived1570 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1569 := derived1569 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1260 := derived1260 a h
  have h8 : Entails.eval a c1541 := derived1541 a h
  have h9 : Entails.eval a c1481 := derived1481 a h
  have h10 : Entails.eval a c1080 := derived1080 a h
  have h11 : Entails.eval a c392 := h 391 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c11 := h 10 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c386 := h 385 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  have h18 : Entails.eval a c1519 := derived1519 a h
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c381 := h 380 (by decide)
  have h21 : Entails.eval a c248 := h 247 (by decide)
  have h22 : Entails.eval a c264 := h 263 (by decide)
  have h23 : Entails.eval a c265 := h 264 (by decide)
  have h24 : Entails.eval a c54 := h 53 (by decide)
  have h25 : Entails.eval a c34 := h 33 (by decide)
  have h26 : Entails.eval a c1516 := derived1516 a h
  have h27 : Entails.eval a c1529 := derived1529 a h
  have h28 : Entails.eval a c326 := h 325 (by decide)
  have h29 : Entails.eval a c322 := h 321 (by decide)
  have h30 : Entails.eval a c152 := h 151 (by decide)
  have h31 : Entails.eval a c1504 := derived1504 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1572 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1570, some c1554, some c202, some c1569, some c201, some c1260, some c1541, some c1481, some c326, some c322, some c152, some c1003, some c1504, some c840, some c1516, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1572 : lratChecker f1572 p1572 = .success := by decide +kernel
theorem unsat1572 : Unsatisfiable (PosFin 57) f1572 := by
  apply lratCheckerSound f1572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1572
  · intro a ha; simp [p1572] at ha; subst a; trivial
  · exact checked1572
theorem derived1572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1572 := by
  apply localUnsat_implies_entails f1572 [c1432, c1431, c1570, c1554, c202, c1569, c201, c1260, c1541, c1481, c326, c322, c152, c1003, c1504, c840, c1516] c1572 unsat1572 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1570 := derived1570 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1569 := derived1569 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1260 := derived1260 a h
  have h8 : Entails.eval a c1541 := derived1541 a h
  have h9 : Entails.eval a c1481 := derived1481 a h
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c322 := h 321 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c1003 := derived1003 a h
  have h14 : Entails.eval a c1504 := derived1504 a h
  have h15 : Entails.eval a c840 := derived840 a h
  have h16 : Entails.eval a c1516 := derived1516 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1573 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1554, some c202, some c1571, some c1259, some c1569, some c201, some c1260, some c1541, some c1481, some c1572, some c985, some c62, some c34, some c37, some c29, some c137, some c174, some c292, some c47, some c98, some c1262, some c384, some c181, some c297, some c102, some c11, some c212, some c314, some c80, some c145, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1573 : lratChecker f1573 p1573 = .success := by decide +kernel
theorem unsat1573 : Unsatisfiable (PosFin 57) f1573 := by
  apply lratCheckerSound f1573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1573
  · intro a ha; simp [p1573] at ha; subst a; trivial
  · exact checked1573
theorem derived1573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1573 := by
  apply localUnsat_implies_entails f1573 [c1432, c1431, c1554, c202, c1571, c1259, c1569, c201, c1260, c1541, c1481, c1572, c985, c62, c34, c37, c29, c137, c174, c292, c47, c98, c1262, c384, c181, c297, c102, c11, c212, c314, c80, c145] c1573 unsat1573 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1571 := derived1571 a h
  have h5 : Entails.eval a c1259 := derived1259 a h
  have h6 : Entails.eval a c1569 := derived1569 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c1260 := derived1260 a h
  have h9 : Entails.eval a c1541 := derived1541 a h
  have h10 : Entails.eval a c1481 := derived1481 a h
  have h11 : Entails.eval a c1572 := derived1572 a h
  have h12 : Entails.eval a c985 := derived985 a h
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c174 := h 173 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c98 := h 97 (by decide)
  have h22 : Entails.eval a c1262 := derived1262 a h
  have h23 : Entails.eval a c384 := h 383 (by decide)
  have h24 : Entails.eval a c181 := h 180 (by decide)
  have h25 : Entails.eval a c297 := h 296 (by decide)
  have h26 : Entails.eval a c102 := h 101 (by decide)
  have h27 : Entails.eval a c11 := h 10 (by decide)
  have h28 : Entails.eval a c212 := h 211 (by decide)
  have h29 : Entails.eval a c314 := h 313 (by decide)
  have h30 : Entails.eval a c80 := h 79 (by decide)
  have h31 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1574 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1481, some c1554, some c202, some c1253, some c1569, some c201, some c1260, some c1573, some c148, some c159, some c1424, some c84, some c1530, some c1519, some c215, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1574 : lratChecker f1574 p1574 = .success := by decide +kernel
theorem unsat1574 : Unsatisfiable (PosFin 57) f1574 := by
  apply lratCheckerSound f1574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1574
  · intro a ha; simp [p1574] at ha; subst a; trivial
  · exact checked1574
theorem derived1574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1574 := by
  apply localUnsat_implies_entails f1574 [c1432, c1481, c1554, c202, c1253, c1569, c201, c1260, c1573, c148, c159, c1424, c84, c1530, c1519, c215] c1574 unsat1574 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c1554 := derived1554 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c1569 := derived1569 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1260 := derived1260 a h
  have h8 : Entails.eval a c1573 := derived1573 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c1424 := derived1424 a h
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c1530 := derived1530 a h
  have h14 : Entails.eval a c1519 := derived1519 a h
  have h15 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1575 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1574, some c1431, some c15, some c7, some c321, some c318, some c570, some c29, some c464, some c43, some c85, some c255, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1575 : lratChecker f1575 p1575 = .success := by decide +kernel
theorem unsat1575 : Unsatisfiable (PosFin 57) f1575 := by
  apply lratCheckerSound f1575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1575
  · intro a ha; simp [p1575] at ha; subst a; trivial
  · exact checked1575
theorem derived1575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1575 := by
  apply localUnsat_implies_entails f1575 [c1432, c1574, c1431, c15, c7, c321, c318, c570, c29, c464, c43, c85, c255] c1575 unsat1575 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c1431 := derived1431 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c570 := derived570 a h
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c464 := derived464 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1576 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1574, some c15, some c7, some c1575, some c33, some c1435, some c37, some c29, some c464, some c291, some c266, some c43, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1576 : lratChecker f1576 p1576 = .success := by decide +kernel
theorem unsat1576 : Unsatisfiable (PosFin 57) f1576 := by
  apply lratCheckerSound f1576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1576
  · intro a ha; simp [p1576] at ha; subst a; trivial
  · exact checked1576
theorem derived1576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1576 := by
  apply localUnsat_implies_entails f1576 [c1431, c1432, c1574, c15, c7, c1575, c33, c1435, c37, c29, c464, c291, c266, c43] c1576 unsat1576 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c1575 := derived1575 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c1435 := derived1435 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c464 := derived464 a h
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1577 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c59, some c204, some c514, some c57, some c122, some c1367, some c53, some c210, some c130, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1577 : lratChecker f1577 p1577 = .success := by decide +kernel
theorem unsat1577 : Unsatisfiable (PosFin 57) f1577 := by
  apply lratCheckerSound f1577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1577
  · intro a ha; simp [p1577] at ha; subst a; trivial
  · exact checked1577
theorem derived1577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1577 := by
  apply localUnsat_implies_entails f1577 [c1431, c59, c204, c514, c57, c122, c1367, c53, c210, c130] c1577 unsat1577 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c514 := derived514 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c1367 := derived1367 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1578 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1431, some c1574, some c202, some c1576, some c123, some c24, some c15, some c7, some c29, some c128, some c1577, some c21, some c122, some c1254, some c1370, some c176, some c304, some c85, some c43, some c255, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1578 : lratChecker f1578 p1578 = .success := by decide +kernel
theorem unsat1578 : Unsatisfiable (PosFin 57) f1578 := by
  apply lratCheckerSound f1578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1578
  · intro a ha; simp [p1578] at ha; subst a; trivial
  · exact checked1578
theorem derived1578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1578 := by
  apply localUnsat_implies_entails f1578 [c1432, c1431, c1574, c202, c1576, c123, c24, c15, c7, c29, c128, c1577, c21, c122, c1254, c1370, c176, c304, c85, c43, c255] c1578 unsat1578 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1576 := derived1576 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c1577 := derived1577 a h
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c1254 := derived1254 a h
  have h15 : Entails.eval a c1370 := derived1370 a h
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c304 := h 303 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c43 := h 42 (by decide)
  have h20 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1579 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1574, some c1576, some c123, some c24, some c202, some c1578, some c1146, some c85, some c107, some c176, some c1254, some c122, some c425, some c21, some c1071, some c204, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1579 : lratChecker f1579 p1579 = .success := by decide +kernel
theorem unsat1579 : Unsatisfiable (PosFin 57) f1579 := by
  apply lratCheckerSound f1579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1579
  · intro a ha; simp [p1579] at ha; subst a; trivial
  · exact checked1579
theorem derived1579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1579 := by
  apply localUnsat_implies_entails f1579 [c1431, c1432, c1574, c1576, c123, c24, c202, c1578, c1146, c85, c107, c176, c1254, c122, c425, c21, c1071, c204] c1579 unsat1579 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c1576 := derived1576 a h
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c1578 := derived1578 a h
  have h8 : Entails.eval a c1146 := derived1146 a h
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c176 := h 175 (by decide)
  have h12 : Entails.eval a c1254 := derived1254 a h
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c425 := derived425 a h
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c1071 := derived1071 a h
  have h17 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1580 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1431, some c1576, some c7, some c123, some c24, some c1579, some c1253, some c1382, some c122, some c323, some c21, some c57, some c59, some c205, some c204, some c514, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1580 : lratChecker f1580 p1580 = .success := by decide +kernel
theorem unsat1580 : Unsatisfiable (PosFin 57) f1580 := by
  apply lratCheckerSound f1580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1580
  · intro a ha; simp [p1580] at ha; subst a; trivial
  · exact checked1580
theorem derived1580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1580 := by
  apply localUnsat_implies_entails f1580 [c1574, c1431, c1576, c7, c123, c24, c1579, c1253, c1382, c122, c323, c21, c57, c59, c205, c204, c514] c1580 unsat1580 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1579 := derived1579 a h
  have h7 : Entails.eval a c1253 := derived1253 a h
  have h8 : Entails.eval a c1382 := derived1382 a h
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c514 := derived514 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1581 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1431, some c1432, some c1346, some c122, some c202, some c1502, some c29, some c1501, some c128, some c1521, some c227, some c125, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1581 : lratChecker f1581 p1581 = .success := by decide +kernel
theorem unsat1581 : Unsatisfiable (PosFin 57) f1581 := by
  apply lratCheckerSound f1581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1581
  · intro a ha; simp [p1581] at ha; subst a; trivial
  · exact checked1581
theorem derived1581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1581 := by
  apply localUnsat_implies_entails f1581 [c1574, c1431, c1432, c1346, c122, c202, c1502, c29, c1501, c128, c1521, c227, c125] c1581 unsat1581 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1432 := derived1432 a h
  have h3 : Entails.eval a c1346 := derived1346 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1502 := derived1502 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c1501 := derived1501 a h
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c1521 := derived1521 a h
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1582 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1574, some c15, some c7, some c1146, some c85, some c106, some c291, some c315, some c43, some c31, some c263, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1582 : lratChecker f1582 p1582 = .success := by decide +kernel
theorem unsat1582 : Unsatisfiable (PosFin 57) f1582 := by
  apply lratCheckerSound f1582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1582
  · intro a ha; simp [p1582] at ha; subst a; trivial
  · exact checked1582
theorem derived1582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1582 := by
  apply localUnsat_implies_entails f1582 [c1431, c1574, c15, c7, c1146, c85, c106, c291, c315, c43, c31, c263] c1582 unsat1582 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1146 := derived1146 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1583 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1431, some c1576, some c15, some c7, some c1580, some c1346, some c1530, some c1387, some c122, some c21, some c204, some c24, some c1582, some c1501, some c57, some c1581, some c157, some c144, some c1500, some c326, some c80, some c286, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1583 : lratChecker f1583 p1583 = .success := by decide +kernel
theorem unsat1583 : Unsatisfiable (PosFin 57) f1583 := by
  apply lratCheckerSound f1583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1583
  · intro a ha; simp [p1583] at ha; subst a; trivial
  · exact checked1583
theorem derived1583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1583 := by
  apply localUnsat_implies_entails f1583 [c1574, c1431, c1576, c15, c7, c1580, c1346, c1530, c1387, c122, c21, c204, c24, c1582, c1501, c57, c1581, c157, c144, c1500, c326, c80, c286] c1583 unsat1583 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c1580 := derived1580 a h
  have h6 : Entails.eval a c1346 := derived1346 a h
  have h7 : Entails.eval a c1530 := derived1530 a h
  have h8 : Entails.eval a c1387 := derived1387 a h
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c1582 := derived1582 a h
  have h14 : Entails.eval a c1501 := derived1501 a h
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c1581 := derived1581 a h
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c1500 := derived1500 a h
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1584 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1432, some c1574, some c1583, some c28, some c15, some c29, some c1003, some c126, some c255, some c56, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1584 : lratChecker f1584 p1584 = .success := by decide +kernel
theorem unsat1584 : Unsatisfiable (PosFin 57) f1584 := by
  apply lratCheckerSound f1584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1584
  · intro a ha; simp [p1584] at ha; subst a; trivial
  · exact checked1584
theorem derived1584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1584 := by
  apply localUnsat_implies_entails f1584 [c1431, c1432, c1574, c1583, c28, c15, c29, c1003, c126, c255, c56] c1584 unsat1584 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c1583 := derived1583 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c255 := h 254 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1585 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1574, some c1576, some c1583, some c520, some c1584, some c1242, some c1582, some c1382, some c123, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1585 : lratChecker f1585 p1585 = .success := by decide +kernel
theorem unsat1585 : Unsatisfiable (PosFin 57) f1585 := by
  apply lratCheckerSound f1585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1585
  · intro a ha; simp [p1585] at ha; subst a; trivial
  · exact checked1585
theorem derived1585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1585 := by
  apply localUnsat_implies_entails f1585 [c1432, c1574, c1576, c1583, c520, c1584, c1242, c1582, c1382, c123] c1585 unsat1585 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1583 := derived1583 a h
  have h4 : Entails.eval a c520 := derived520 a h
  have h5 : Entails.eval a c1584 := derived1584 a h
  have h6 : Entails.eval a c1242 := derived1242 a h
  have h7 : Entails.eval a c1582 := derived1582 a h
  have h8 : Entails.eval a c1382 := derived1382 a h
  have h9 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1586 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1432, some c201, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1586 : lratChecker f1586 p1586 = .success := by decide +kernel
theorem unsat1586 : Unsatisfiable (PosFin 57) f1586 := by
  apply lratCheckerSound f1586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1586
  · intro a ha; simp [p1586] at ha; subst a; trivial
  · exact checked1586
theorem derived1586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1586 := by
  apply localUnsat_implies_entails f1586 [c1585, c1432, c201] c1586 unsat1586 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1587 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1432, some c203, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1587 : lratChecker f1587 p1587 = .success := by decide +kernel
theorem unsat1587 : Unsatisfiable (PosFin 57) f1587 := by
  apply lratCheckerSound f1587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1587
  · intro a ha; simp [p1587] at ha; subst a; trivial
  · exact checked1587
theorem derived1587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1587 := by
  apply localUnsat_implies_entails f1587 [c1585, c1432, c203] c1587 unsat1587 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1588 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1586, some c1587, some c1260, some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1588 : lratChecker f1588 p1588 = .success := by decide +kernel
theorem unsat1588 : Unsatisfiable (PosFin 57) f1588 := by
  apply lratCheckerSound f1588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1588
  · intro a ha; simp [p1588] at ha; subst a; trivial
  · exact checked1588
theorem derived1588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1588 := by
  apply localUnsat_implies_entails f1588 [c1586, c1587, c1260] c1588 unsat1588 (by rfl) a
  have h0 : Entails.eval a c1586 := derived1586 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1260 := derived1260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1589 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1253, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1589 : lratChecker f1589 p1589 = .success := by decide +kernel
theorem unsat1589 : Unsatisfiable (PosFin 57) f1589 := by
  apply lratCheckerSound f1589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1589
  · intro a ha; simp [p1589] at ha; subst a; trivial
  · exact checked1589
theorem derived1589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1589 := by
  apply localUnsat_implies_entails f1589 [c1587, c1253] c1589 unsat1589 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1590 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1585, some c1587, some c1588, some c1423, some c498, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1590 : lratChecker f1590 p1590 = .success := by decide +kernel
theorem unsat1590 : Unsatisfiable (PosFin 57) f1590 := by
  apply lratCheckerSound f1590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1590
  · intro a ha; simp [p1590] at ha; subst a; trivial
  · exact checked1590
theorem derived1590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1590 := by
  apply localUnsat_implies_entails f1590 [c1432, c1585, c1587, c1588, c1423, c498] c1590 unsat1590 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1588 := derived1588 a h
  have h4 : Entails.eval a c1423 := derived1423 a h
  have h5 : Entails.eval a c498 := derived498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1591 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1586, some c1588, some c1587, some c1589, some c1432, some c1431, some c1574, some c122, some c1259, some c1590, some c1484, some c1449, some c123, some c4, some c316, some c158, some c145, some c78, some c353, some c169, some c83, some c214, some c282, some c126, some c324, some c29, some c61, some c323, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1591 : lratChecker f1591 p1591 = .success := by decide +kernel
theorem unsat1591 : Unsatisfiable (PosFin 57) f1591 := by
  apply lratCheckerSound f1591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1591
  · intro a ha; simp [p1591] at ha; subst a; trivial
  · exact checked1591
theorem derived1591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1591 := by
  apply localUnsat_implies_entails f1591 [c1586, c1588, c1587, c1589, c1432, c1431, c1574, c122, c1259, c1590, c1484, c1449, c123, c4, c316, c158, c145, c78, c353, c169, c83, c214, c282, c126, c324, c29, c61, c323] c1591 unsat1591 (by rfl) a
  have h0 : Entails.eval a c1586 := derived1586 a h
  have h1 : Entails.eval a c1588 := derived1588 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1589 := derived1589 a h
  have h4 : Entails.eval a c1432 := derived1432 a h
  have h5 : Entails.eval a c1431 := derived1431 a h
  have h6 : Entails.eval a c1574 := derived1574 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c1259 := derived1259 a h
  have h9 : Entails.eval a c1590 := derived1590 a h
  have h10 : Entails.eval a c1484 := derived1484 a h
  have h11 : Entails.eval a c1449 := derived1449 a h
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c145 := h 144 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c83 := h 82 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c282 := h 281 (by decide)
  have h23 : Entails.eval a c126 := h 125 (by decide)
  have h24 : Entails.eval a c324 := h 323 (by decide)
  have h25 : Entails.eval a c29 := h 28 (by decide)
  have h26 : Entails.eval a c61 := h 60 (by decide)
  have h27 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1592 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1574, some c1589, some c1587, some c1585, some c1431, some c1588, some c29, some c127, some c35, some c43, some c318, some c175, some c302, some c85, some c1061, some c253, some c1258, some c41, some c183, some c123, some c723, some c59, some c316, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1592 : lratChecker f1592 p1592 = .success := by decide +kernel
theorem unsat1592 : Unsatisfiable (PosFin 57) f1592 := by
  apply lratCheckerSound f1592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1592
  · intro a ha; simp [p1592] at ha; subst a; trivial
  · exact checked1592
theorem derived1592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1592 := by
  apply localUnsat_implies_entails f1592 [c1432, c1574, c1589, c1587, c1585, c1431, c1588, c29, c127, c35, c43, c318, c175, c302, c85, c1061, c253, c1258, c41, c183, c123, c723, c59, c316] c1592 unsat1592 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c1589 := derived1589 a h
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c1585 := derived1585 a h
  have h5 : Entails.eval a c1431 := derived1431 a h
  have h6 : Entails.eval a c1588 := derived1588 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c175 := h 174 (by decide)
  have h13 : Entails.eval a c302 := h 301 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c1061 := derived1061 a h
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c1258 := derived1258 a h
  have h18 : Entails.eval a c41 := h 40 (by decide)
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c723 := derived723 a h
  have h22 : Entails.eval a c59 := h 58 (by decide)
  have h23 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1593 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1588, some c1431, some c1432, some c1589, some c1574, some c1585, some c1592, some c305, some c321, some c85, some c35, some c175, some c289, some c561, some c91, some c123, some c567, some c41, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1593 : lratChecker f1593 p1593 = .success := by decide +kernel
theorem unsat1593 : Unsatisfiable (PosFin 57) f1593 := by
  apply lratCheckerSound f1593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1593
  · intro a ha; simp [p1593] at ha; subst a; trivial
  · exact checked1593
theorem derived1593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1593 := by
  apply localUnsat_implies_entails f1593 [c1588, c1431, c1432, c1589, c1574, c1585, c1592, c305, c321, c85, c35, c175, c289, c561, c91, c123, c567, c41] c1593 unsat1593 (by rfl) a
  have h0 : Entails.eval a c1588 := derived1588 a h
  have h1 : Entails.eval a c1431 := derived1431 a h
  have h2 : Entails.eval a c1432 := derived1432 a h
  have h3 : Entails.eval a c1589 := derived1589 a h
  have h4 : Entails.eval a c1574 := derived1574 a h
  have h5 : Entails.eval a c1585 := derived1585 a h
  have h6 : Entails.eval a c1592 := derived1592 a h
  have h7 : Entails.eval a c305 := h 304 (by decide)
  have h8 : Entails.eval a c321 := h 320 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c561 := derived561 a h
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c567 := derived567 a h
  have h17 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1593

end CochromaticTwenty.Certificates.B16_1_2
