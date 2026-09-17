import MerLeanExperiment.Certificates.B16_2_2.Steps1000_1099

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1484 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1476, some c1464, some c1446, some c109, some c106, some c1368, some c1478, some c15, some c1480, some c105, some c1483, some c522, some c39, some c263, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1484 : lratChecker f1484 p1484 = .success := by decide +kernel
theorem unsat1484 : Unsatisfiable (PosFin 57) f1484 := by
  apply lratCheckerSound f1484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1484
  · intro a ha; simp [p1484] at ha; subst a; trivial
  · exact checked1484
theorem derived1484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1484 := by
  apply localUnsat_implies_entails f1484 [c1476, c1464, c1446, c109, c106, c1368, c1478, c15, c1480, c105, c1483, c522, c39, c263] c1484 unsat1484 (by rfl) a
  have h0 : Entails.eval a c1476 := derived1476 a h
  have h1 : Entails.eval a c1464 := derived1464 a h
  have h2 : Entails.eval a c1446 := derived1446 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1368 := derived1368 a h
  have h6 : Entails.eval a c1478 := derived1478 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c1480 := derived1480 a h
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c1483 := derived1483 a h
  have h11 : Entails.eval a c522 := derived522 a h
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1485 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1368, some c1446, some c106, some c109, some c1464, some c1476, some c1484, some c768, some c99, some c3, some c75, some c1014, some c196, some c123, some c1003, some c27, some c105, some c447, some c1332, some c1458, some c715, some c371, some c367, some c240, some c567, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1485 : lratChecker f1485 p1485 = .success := by decide +kernel
theorem unsat1485 : Unsatisfiable (PosFin 57) f1485 := by
  apply lratCheckerSound f1485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1485
  · intro a ha; simp [p1485] at ha; subst a; trivial
  · exact checked1485
theorem derived1485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1485 := by
  apply localUnsat_implies_entails f1485 [c1368, c1446, c106, c109, c1464, c1476, c1484, c768, c99, c3, c75, c1014, c196, c123, c1003, c27, c105, c447, c1332, c1458, c715, c371, c367, c240, c567] c1485 unsat1485 (by rfl) a
  have h0 : Entails.eval a c1368 := derived1368 a h
  have h1 : Entails.eval a c1446 := derived1446 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1464 := derived1464 a h
  have h5 : Entails.eval a c1476 := derived1476 a h
  have h6 : Entails.eval a c1484 := derived1484 a h
  have h7 : Entails.eval a c768 := derived768 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c1014 := derived1014 a h
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c1003 := derived1003 a h
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c447 := derived447 a h
  have h18 : Entails.eval a c1332 := derived1332 a h
  have h19 : Entails.eval a c1458 := derived1458 a h
  have h20 : Entails.eval a c715 := derived715 a h
  have h21 : Entails.eval a c371 := h 370 (by decide)
  have h22 : Entails.eval a c367 := h 366 (by decide)
  have h23 : Entails.eval a c240 := h 239 (by decide)
  have h24 : Entails.eval a c567 := derived567 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1486 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c102, some c103, some c589, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1486 : lratChecker f1486 p1486 = .success := by decide +kernel
theorem unsat1486 : Unsatisfiable (PosFin 57) f1486 := by
  apply lratCheckerSound f1486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1486
  · intro a ha; simp [p1486] at ha; subst a; trivial
  · exact checked1486
theorem derived1486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1486 := by
  apply localUnsat_implies_entails f1486 [c383, c102, c103, c589] c1486 unsat1486 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c589 := derived589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1487 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨24, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c13, some c105, some c107, some c12, some c195, some c1399, some c2, some c381, some c248, some c6, some c78, some c22, some c32, some c173, some c373, some c124, some c1147, some c1143, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1487 : lratChecker f1487 p1487 = .success := by decide +kernel
theorem unsat1487 : Unsatisfiable (PosFin 57) f1487 := by
  apply lratCheckerSound f1487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1487
  · intro a ha; simp [p1487] at ha; subst a; trivial
  · exact checked1487
theorem derived1487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1487 := by
  apply localUnsat_implies_entails f1487 [c1485, c1254, c13, c105, c107, c12, c195, c1399, c2, c381, c248, c6, c78, c22, c32, c173, c373, c124, c1147, c1143] c1487 unsat1487 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c1399 := derived1399 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c173 := h 172 (by decide)
  have h16 : Entails.eval a c373 := h 372 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c1147 := derived1147 a h
  have h19 : Entails.eval a c1143 := derived1143 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1488 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c38, some c262, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1488 : lratChecker f1488 p1488 = .success := by decide +kernel
theorem unsat1488 : Unsatisfiable (PosFin 57) f1488 := by
  apply lratCheckerSound f1488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1488
  · intro a ha; simp [p1488] at ha; subst a; trivial
  · exact checked1488
theorem derived1488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1488 := by
  apply localUnsat_implies_entails f1488 [c32, c38, c262] c1488 unsat1488 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1489 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c13, some c105, some c107, some c12, some c2, some c379, some c1486, some c184, some c195, some c1399, some c1487, some c101, some c1488, some c124, some c1256, some c1203, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 57) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c1485, c1254, c13, c105, c107, c12, c2, c379, c1486, c184, c195, c1399, c1487, c101, c1488, c124, c1256, c1203] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1486 := derived1486 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c1399 := derived1399 a h
  have h12 : Entails.eval a c1487 := derived1487 a h
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c1488 := derived1488 a h
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c1256 := derived1256 a h
  have h17 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1485, some c13, some c105, some c12, some c107, some c2, some c379, some c1486, some c184, some c195, some c1399, some c1489, some c28, some c39, some c124, some c37, some c1203, some c1259, some c257, some c381, some c1255, some c78, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 57) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1254, c1485, c13, c105, c12, c107, c2, c379, c1486, c184, c195, c1399, c1489, c28, c39, c124, c37, c1203, c1259, c257, c381, c1255, c78] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1486 := derived1486 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c1399 := derived1399 a h
  have h12 : Entails.eval a c1489 := derived1489 a h
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c1203 := derived1203 a h
  have h18 : Entails.eval a c1259 := derived1259 a h
  have h19 : Entails.eval a c257 := h 256 (by decide)
  have h20 : Entails.eval a c381 := h 380 (by decide)
  have h21 : Entails.eval a c1255 := derived1255 a h
  have h22 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c799, some c800, some c136, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 57) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c8, c799, c800, c136] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c799 := derived799 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c105, some c1488, some c1254, some c12, some c195, some c2, some c381, some c248, some c378, some c6, some c78, some c102, some c726, some c22, some c190, some c1143, some c372, some c179, some c170, some c252, some c357, some c701, some c368, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 57) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c1485, c105, c1488, c1254, c12, c195, c2, c381, c248, c378, c6, c78, c102, c726, c22, c190, c1143, c372, c179, c170, c252, c357, c701, c368] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1488 := derived1488 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c726 := derived726 a h
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c1143 := derived1143 a h
  have h17 : Entails.eval a c372 := h 371 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c170 := h 169 (by decide)
  have h20 : Entails.eval a c252 := h 251 (by decide)
  have h21 : Entails.eval a c357 := h 356 (by decide)
  have h22 : Entails.eval a c701 := derived701 a h
  have h23 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1485, some c2, some c13, some c107, some c1491, some c105, some c12, some c195, some c1391, some c1490, some c1492, some c103, some c80, some c376, some c726, some c380, some c179, some c116, some c1052, some c51, some c144, some c101, some c49, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 57) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1254, c1485, c2, c13, c107, c1491, c105, c12, c195, c1391, c1490, c1492, c103, c80, c376, c726, c380, c179, c116, c1052, c51, c144, c101, c49] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1491 := derived1491 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c1391 := derived1391 a h
  have h10 : Entails.eval a c1490 := derived1490 a h
  have h11 : Entails.eval a c1492 := derived1492 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c726 := derived726 a h
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c1052 := derived1052 a h
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c144 := h 143 (by decide)
  have h22 : Entails.eval a c101 := h 100 (by decide)
  have h23 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1494 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1485, some c13, some c105, some c12, some c195, some c1490, some c107, some c2, some c1491, some c1493, some c28, some c726, some c589, some c380, some c103, some c376, some c179, some c164, some c357, some c358, some c170, some c371, some c84, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 57) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1254, c1485, c13, c105, c12, c195, c1490, c107, c2, c1491, c1493, c28, c726, c589, c380, c103, c376, c179, c164, c357, c358, c170, c371, c84] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c1490 := derived1490 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1491 := derived1491 a h
  have h10 : Entails.eval a c1493 := derived1493 a h
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c726 := derived726 a h
  have h13 : Entails.eval a c589 := derived589 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  have h20 : Entails.eval a c358 := h 357 (by decide)
  have h21 : Entails.eval a c170 := h 169 (by decide)
  have h22 : Entails.eval a c371 := h 370 (by decide)
  have h23 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c107, some c1485, some c8, some c17, some c1242, some c248, some c22, some c373, some c372, some c1143, some c236, some c170, some c368, some c357, some c230, some c244, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 57) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c195, c107, c1485, c8, c17, c1242, c248, c22, c373, c372, c1143, c236, c170, c368, c357, c230, c244] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c1242 := derived1242 a h
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c1143 := derived1143 a h
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c230 := h 229 (by decide)
  have h16 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c13, some c2, some c1320, some c298, some c144, some c139, some c43, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 57) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1485, c13, c2, c1320, c298, c144, c139, c43] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1320 := derived1320 a h
  have h4 : Entails.eval a c298 := h 297 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1485, some c1254, some c2, some c380, some c102, some c78, some c12, some c1488, some c252, some c1495, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 57) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c105, c1485, c1254, c2, c380, c102, c78, c12, c1488, c252, c1495] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c1488 := derived1488 a h
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c1495 := derived1495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1490, some c1254, some c1485, some c13, some c105, some c12, some c107, some c2, some c1391, some c195, some c1494, some c184, some c380, some c6, some c78, some c1496, some c190, some c162, some c1497, some c28, some c39, some c373, some c113, some c84, some c230, some c170, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 57) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1490, c1254, c1485, c13, c105, c12, c107, c2, c1391, c195, c1494, c184, c380, c6, c78, c1496, c190, c162, c1497, c28, c39, c373, c113, c84, c230, c170] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1490 := derived1490 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c1391 := derived1391 a h
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c1494 := derived1494 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c1496 := derived1496 a h
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c1497 := derived1497 a h
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c39 := h 38 (by decide)
  have h21 : Entails.eval a c373 := h 372 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c84 := h 83 (by decide)
  have h24 : Entails.eval a c230 := h 229 (by decide)
  have h25 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨21, by decide⟩, false), (⟨16, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c6, some c102, some c190, some c254, some c634, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 57) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c105, c6, c102, c190, c254, c634] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c254 := h 253 (by decide)
  have h5 : Entails.eval a c634 := derived634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1254, some c1485, some c2, some c13, some c107, some c1491, some c1490, some c1498, some c3, some c105, some c12, some c1488, some c1499, some c589, some c1034, some c1259, some c1203, some c634, some c124, some c116, some c1052, some c49, some c51, some c144, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 57) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1254, c1485, c2, c13, c107, c1491, c1490, c1498, c3, c105, c12, c1488, c1499, c589, c1034, c1259, c1203, c634, c124, c116, c1052, c49, c51, c144] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1491 := derived1491 a h
  have h6 : Entails.eval a c1490 := derived1490 a h
  have h7 : Entails.eval a c1498 := derived1498 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c1488 := derived1488 a h
  have h12 : Entails.eval a c1499 := derived1499 a h
  have h13 : Entails.eval a c589 := derived589 a h
  have h14 : Entails.eval a c1034 := derived1034 a h
  have h15 : Entails.eval a c1259 := derived1259 a h
  have h16 : Entails.eval a c1203 := derived1203 a h
  have h17 : Entails.eval a c634 := derived634 a h
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c1052 := derived1052 a h
  have h21 : Entails.eval a c49 := h 48 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1490, some c1498, some c3, some c1254, some c1485, some c13, some c105, some c12, some c107, some c2, some c1491, some c1500, some c28, some c39, some c726, some c589, some c1034, some c1259, some c1203, some c634, some c124, some c113, some c1052, some c49, some c51, some c144, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 57) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1490, c1498, c3, c1254, c1485, c13, c105, c12, c107, c2, c1491, c1500, c28, c39, c726, c589, c1034, c1259, c1203, c634, c124, c113, c1052, c49, c51, c144] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1490 := derived1490 a h
  have h1 : Entails.eval a c1498 := derived1498 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c1485 := derived1485 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c1491 := derived1491 a h
  have h11 : Entails.eval a c1500 := derived1500 a h
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c726 := derived726 a h
  have h15 : Entails.eval a c589 := derived589 a h
  have h16 : Entails.eval a c1034 := derived1034 a h
  have h17 : Entails.eval a c1259 := derived1259 a h
  have h18 : Entails.eval a c1203 := derived1203 a h
  have h19 : Entails.eval a c634 := derived634 a h
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c113 := h 112 (by decide)
  have h22 : Entails.eval a c1052 := derived1052 a h
  have h23 : Entails.eval a c49 := h 48 (by decide)
  have h24 : Entails.eval a c51 := h 50 (by decide)
  have h25 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c13, some c105, some c1488, some c1501, some c1490, some c1498, some c3, some c107, some c2, some c8, some c381, some c1487, some c6, some c102, some c184, some c17, some c252, some c1242, some c669, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 57) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1485, c1254, c13, c105, c1488, c1501, c1490, c1498, c3, c107, c2, c8, c381, c1487, c6, c102, c184, c17, c252, c1242, c669] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c1488 := derived1488 a h
  have h5 : Entails.eval a c1501 := derived1501 a h
  have h6 : Entails.eval a c1490 := derived1490 a h
  have h7 : Entails.eval a c1498 := derived1498 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c381 := h 380 (by decide)
  have h13 : Entails.eval a c1487 := derived1487 a h
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  have h19 : Entails.eval a c1242 := derived1242 a h
  have h20 : Entails.eval a c669 := derived669 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨55, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c13, some c107, some c6, some c726, some c190, some c80, some c1487, some c184, some c1496, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 57) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1485, c1254, c13, c107, c6, c726, c190, c80, c1487, c184, c1496] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c726 := derived726 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c1487 := derived1487 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c1496 := derived1496 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1501, some c1490, some c1498, some c3, some c1254, some c1485, some c13, some c105, some c12, some c107, some c2, some c1488, some c1502, some c1503, some c1034, some c380, some c381, some c184, some c1256, some c124, some c1203, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 57) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1501, c1490, c1498, c3, c1254, c1485, c13, c105, c12, c107, c2, c1488, c1502, c1503, c1034, c380, c381, c184, c1256, c124, c1203] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1501 := derived1501 a h
  have h1 : Entails.eval a c1490 := derived1490 a h
  have h2 : Entails.eval a c1498 := derived1498 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1254 := derived1254 a h
  have h5 : Entails.eval a c1485 := derived1485 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c1488 := derived1488 a h
  have h12 : Entails.eval a c1502 := derived1502 a h
  have h13 : Entails.eval a c1503 := derived1503 a h
  have h14 : Entails.eval a c1034 := derived1034 a h
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c381 := h 380 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c1256 := derived1256 a h
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨45, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c13, some c105, some c107, some c39, some c12, some c37, some c1203, some c1147, some c1242, some c172, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 57) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c1485, c13, c105, c107, c39, c12, c37, c1203, c1147, c1242, c172] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1203 := derived1203 a h
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c1242 := derived1242 a h
  have h10 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c13, some c105, some c107, some c1504, some c39, some c28, some c1501, some c1490, some c1498, some c3, some c12, some c2, some c8, some c381, some c78, some c102, some c373, some c84, some c1505, some c252, some c124, some c184, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 57) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c1485, c1254, c13, c105, c107, c1504, c39, c28, c1501, c1490, c1498, c3, c12, c2, c8, c381, c78, c102, c373, c84, c1505, c252, c124, c184] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c1504 := derived1504 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c1501 := derived1501 a h
  have h9 : Entails.eval a c1490 := derived1490 a h
  have h10 : Entails.eval a c1498 := derived1498 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c84 := h 83 (by decide)
  have h20 : Entails.eval a c1505 := derived1505 a h
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1490, some c1254, some c1485, some c13, some c105, some c12, some c107, some c2, some c1498, some c3, some c1501, some c1504, some c28, some c39, some c1506, some c726, some c1034, some c380, some c381, some c184, some c1256, some c124, some c1203, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 57) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1490, c1254, c1485, c13, c105, c12, c107, c2, c1498, c3, c1501, c1504, c28, c39, c1506, c726, c1034, c380, c381, c184, c1256, c124, c1203] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1490 := derived1490 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c1498 := derived1498 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1501 := derived1501 a h
  have h11 : Entails.eval a c1504 := derived1504 a h
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c1506 := derived1506 a h
  have h15 : Entails.eval a c726 := derived726 a h
  have h16 : Entails.eval a c1034 := derived1034 a h
  have h17 : Entails.eval a c380 := h 379 (by decide)
  have h18 : Entails.eval a c381 := h 380 (by decide)
  have h19 : Entails.eval a c184 := h 183 (by decide)
  have h20 : Entails.eval a c1256 := derived1256 a h
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c1488, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 57) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c39, c1488] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c1488 := derived1488 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1509 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1254, some c2, some c13, some c105, some c107, some c12, some c1490, some c1507, some c1508, some c122, some c263, some c264, some c3, some c1203, some c634, some c1034, some c113, some c6, some c685, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 57) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1485, c1254, c2, c13, c105, c107, c12, c1490, c1507, c1508, c122, c263, c264, c3, c1203, c634, c1034, c113, c6, c685] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c1490 := derived1490 a h
  have h8 : Entails.eval a c1507 := derived1507 a h
  have h9 : Entails.eval a c1508 := derived1508 a h
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c1203 := derived1203 a h
  have h15 : Entails.eval a c634 := derived634 a h
  have h16 : Entails.eval a c1034 := derived1034 a h
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c685 := derived685 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨10, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c74, some c120, some c248, some c8, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 57) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c22, c74, c120, c248, c8] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c378, some c33, some c27, some c262, some c248, some c234, some c96, some c543, some c383, some c91, some c357, some c368, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 57) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c256, c378, c33, c27, c262, c248, c234, c96, c543, c383, c91, c357, c368] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c543 := derived543 a h
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c1341, some c7, some c1510, some c165, some c23, some c111, some c1511, some c8, some c80, some c168, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 57) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c13, c1341, c7, c1510, c165, c23, c111, c1511, c8, c80, c168] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c1341 := derived1341 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1510 := derived1510 a h
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1511 := derived1511 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨43, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c447, some c1509, some c106, some c1485, some c19, some c195, some c170, some c84, some c1143, some c25, some c165, some c371, some c373, some c2, some c1491, some c1237, some c184, some c367, some c252, some c1496, some c370, some c231, some c113, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 57) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c105, c447, c1509, c106, c1485, c19, c195, c170, c84, c1143, c25, c165, c371, c373, c2, c1491, c1237, c184, c367, c252, c1496, c370, c231, c113] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c447 := derived447 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1485 := derived1485 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c1143 := derived1143 a h
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c371 := h 370 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c1491 := derived1491 a h
  have h16 : Entails.eval a c1237 := derived1237 a h
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c367 := h 366 (by decide)
  have h19 : Entails.eval a c252 := h 251 (by decide)
  have h20 : Entails.eval a c1496 := derived1496 a h
  have h21 : Entails.eval a c370 := h 369 (by decide)
  have h22 : Entails.eval a c231 := h 230 (by decide)
  have h23 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨43, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1485, some c1003, some c170, some c84, some c165, some c195, some c1513, some c1509, some c1496, some c1448, some c190, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 57) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c105, c1485, c1003, c170, c84, c165, c195, c1513, c1509, c1496, c1448, c190] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c1513 := derived1513 a h
  have h8 : Entails.eval a c1509 := derived1509 a h
  have h9 : Entails.eval a c1496 := derived1496 a h
  have h10 : Entails.eval a c1448 := derived1448 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1513, some c105, some c447, some c1509, some c106, some c1485, some c1003, some c383, some c376, some c195, some c170, some c99, some c84, some c1143, some c371, some c1514, some c179, some c358, some c164, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 57) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c1513, c105, c447, c1509, c106, c1485, c1003, c383, c376, c195, c170, c99, c84, c1143, c371, c1514, c179, c358, c164] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c1513 := derived1513 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c447 := derived447 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1485 := derived1485 a h
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c1143 := derived1143 a h
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c1514 := derived1514 a h
  have h16 : Entails.eval a c179 := h 178 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c192, some c195, some c12, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 57) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c192, c195, c12] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c1485, some c2, some c1496, some c381, some c190, some c188, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 57) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c184, c1485, c2, c1496, c381, c190, c188] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1496 := derived1496 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1512, some c105, some c1516, some c23, some c447, some c1513, some c1515, some c184, some c382, some c99, some c1517, some c1510, some c165, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 57) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c1485, c1509, c106, c1512, c105, c1516, c23, c447, c1513, c1515, c184, c382, c99, c1517, c1510, c165] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1512 := derived1512 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1516 := derived1516 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c1513 := derived1513 a h
  have h9 : Entails.eval a c1515 := derived1515 a h
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c382 := h 381 (by decide)
  have h12 : Entails.eval a c99 := h 98 (by decide)
  have h13 : Entails.eval a c1517 := derived1517 a h
  have h14 : Entails.eval a c1510 := derived1510 a h
  have h15 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c1003, some c383, some c471, some c77, some c248, some c379, some c32, some c179, some c113, some c161, some c230, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 57) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c378, c1003, c383, c471, c77, c248, c379, c32, c179, c113, c161, c230] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c471 := derived471 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, false), (⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c248, some c609, some c145, some c136, some c298, some c339, some c198, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 57) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c256, c248, c609, c145, c136, c298, c339, c198] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c609 := derived609 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c339 := h 338 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1521 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c1518, some c1485, some c1509, some c106, some c1512, some c105, some c1516, some c8, some c1318, some c1513, some c256, some c589, some c378, some c1519, some c361, some c357, some c369, some c1143, some c161, some c368, some c179, some c1496, some c1510, some c372, some c701, some c1520, some c96, some c252, some c32, some c262, some c1156, some c69, some c58, some c151, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1521 : lratChecker f1521 p1521 = .success := by decide +kernel
theorem unsat1521 : Unsatisfiable (PosFin 57) f1521 := by
  apply lratCheckerSound f1521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1521
  · intro a ha; simp [p1521] at ha; subst a; trivial
  · exact checked1521
theorem derived1521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1521 := by
  apply localUnsat_implies_entails f1521 [c1003, c1518, c1485, c1509, c106, c1512, c105, c1516, c8, c1318, c1513, c256, c589, c378, c1519, c361, c357, c369, c1143, c161, c368, c179, c1496, c1510, c372, c701, c1520, c96, c252, c32, c262, c1156, c69, c58, c151] c1521 unsat1521 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c1518 := derived1518 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1512 := derived1512 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c1318 := derived1318 a h
  have h10 : Entails.eval a c1513 := derived1513 a h
  have h11 : Entails.eval a c256 := h 255 (by decide)
  have h12 : Entails.eval a c589 := derived589 a h
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c1519 := derived1519 a h
  have h15 : Entails.eval a c361 := h 360 (by decide)
  have h16 : Entails.eval a c357 := h 356 (by decide)
  have h17 : Entails.eval a c369 := h 368 (by decide)
  have h18 : Entails.eval a c1143 := derived1143 a h
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c368 := h 367 (by decide)
  have h21 : Entails.eval a c179 := h 178 (by decide)
  have h22 : Entails.eval a c1496 := derived1496 a h
  have h23 : Entails.eval a c1510 := derived1510 a h
  have h24 : Entails.eval a c372 := h 371 (by decide)
  have h25 : Entails.eval a c701 := derived701 a h
  have h26 : Entails.eval a c1520 := derived1520 a h
  have h27 : Entails.eval a c96 := h 95 (by decide)
  have h28 : Entails.eval a c252 := h 251 (by decide)
  have h29 : Entails.eval a c32 := h 31 (by decide)
  have h30 : Entails.eval a c262 := h 261 (by decide)
  have h31 : Entails.eval a c1156 := derived1156 a h
  have h32 : Entails.eval a c69 := h 68 (by decide)
  have h33 : Entails.eval a c58 := h 57 (by decide)
  have h34 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1522 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c379, some c96, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1522 : lratChecker f1522 p1522 = .success := by decide +kernel
theorem unsat1522 : Unsatisfiable (PosFin 57) f1522 := by
  apply lratCheckerSound f1522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1522
  · intro a ha; simp [p1522] at ha; subst a; trivial
  · exact checked1522
theorem derived1522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1522 := by
  apply localUnsat_implies_entails f1522 [c383, c379, c96] c1522 unsat1522 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1523 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1512, some c105, some c1522, some c1521, some c1003, some c1518, some c1516, some c589, some c1514, some c378, some c361, some c357, some c369, some c1143, some c161, some c1496, some c1510, some c194, some c509, some c1330, some c51, some c199, some c65, some c67, some c156, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1523 : lratChecker f1523 p1523 = .success := by decide +kernel
theorem unsat1523 : Unsatisfiable (PosFin 57) f1523 := by
  apply lratCheckerSound f1523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1523
  · intro a ha; simp [p1523] at ha; subst a; trivial
  · exact checked1523
theorem derived1523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1523 := by
  apply localUnsat_implies_entails f1523 [c1485, c1509, c106, c1512, c105, c1522, c1521, c1003, c1518, c1516, c589, c1514, c378, c361, c357, c369, c1143, c161, c1496, c1510, c194, c509, c1330, c51, c199, c65, c67, c156] c1523 unsat1523 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1512 := derived1512 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1522 := derived1522 a h
  have h6 : Entails.eval a c1521 := derived1521 a h
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c1518 := derived1518 a h
  have h9 : Entails.eval a c1516 := derived1516 a h
  have h10 : Entails.eval a c589 := derived589 a h
  have h11 : Entails.eval a c1514 := derived1514 a h
  have h12 : Entails.eval a c378 := h 377 (by decide)
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c1143 := derived1143 a h
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c1496 := derived1496 a h
  have h19 : Entails.eval a c1510 := derived1510 a h
  have h20 : Entails.eval a c194 := h 193 (by decide)
  have h21 : Entails.eval a c509 := derived509 a h
  have h22 : Entails.eval a c1330 := derived1330 a h
  have h23 : Entails.eval a c51 := h 50 (by decide)
  have h24 : Entails.eval a c199 := h 198 (by decide)
  have h25 : Entails.eval a c65 := h 64 (by decide)
  have h26 : Entails.eval a c67 := h 66 (by decide)
  have h27 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1524 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨52, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1509, some c190, some c116, some c1330, some c1052, some c51, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1524 : lratChecker f1524 p1524 = .success := by decide +kernel
theorem unsat1524 : Unsatisfiable (PosFin 57) f1524 := by
  apply lratCheckerSound f1524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1524
  · intro a ha; simp [p1524] at ha; subst a; trivial
  · exact checked1524
theorem derived1524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1524 := by
  apply localUnsat_implies_entails f1524 [c105, c1509, c190, c116, c1330, c1052, c51] c1524 unsat1524 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c190 := h 189 (by decide)
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c1330 := derived1330 a h
  have h5 : Entails.eval a c1052 := derived1052 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1525 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1521, some c1518, some c1485, some c1509, some c106, some c1512, some c105, some c1516, some c1522, some c1523, some c1524, some c1496, some c1510, some c943, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1525 : lratChecker f1525 p1525 = .success := by decide +kernel
theorem unsat1525 : Unsatisfiable (PosFin 57) f1525 := by
  apply lratCheckerSound f1525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1525
  · intro a ha; simp [p1525] at ha; subst a; trivial
  · exact checked1525
theorem derived1525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1525 := by
  apply localUnsat_implies_entails f1525 [c1521, c1518, c1485, c1509, c106, c1512, c105, c1516, c1522, c1523, c1524, c1496, c1510, c943] c1525 unsat1525 (by rfl) a
  have h0 : Entails.eval a c1521 := derived1521 a h
  have h1 : Entails.eval a c1518 := derived1518 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1512 := derived1512 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c1522 := derived1522 a h
  have h9 : Entails.eval a c1523 := derived1523 a h
  have h10 : Entails.eval a c1524 := derived1524 a h
  have h11 : Entails.eval a c1496 := derived1496 a h
  have h12 : Entails.eval a c1510 := derived1510 a h
  have h13 : Entails.eval a c943 := derived943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1526 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c51, some c144, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1526 : lratChecker f1526 p1526 = .success := by decide +kernel
theorem unsat1526 : Unsatisfiable (PosFin 57) f1526 := by
  apply lratCheckerSound f1526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1526
  · intro a ha; simp [p1526] at ha; subst a; trivial
  · exact checked1526
theorem derived1526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1526 := by
  apply localUnsat_implies_entails f1526 [c49, c51, c144] c1526 unsat1526 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1527 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1526, some c199, some c65, some c67, some c156, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1527 : lratChecker f1527 p1527 = .success := by decide +kernel
theorem unsat1527 : Unsatisfiable (PosFin 57) f1527 := by
  apply lratCheckerSound f1527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1527
  · intro a ha; simp [p1527] at ha; subst a; trivial
  · exact checked1527
theorem derived1527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1527 := by
  apply localUnsat_implies_entails f1527 [c1526, c199, c65, c67, c156] c1527 unsat1527 (by rfl) a
  have h0 : Entails.eval a c1526 := derived1526 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1528 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1509, some c106, some c1485, some c1512, some c105, some c1516, some c1518, some c1527, some c1318, some c4, some c1524, some c1525, some c1496, some c1510, some c194, some c165, some c168, some c509, some c188, some c80, some c234, some c255, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1528 : lratChecker f1528 p1528 = .success := by decide +kernel
theorem unsat1528 : Unsatisfiable (PosFin 57) f1528 := by
  apply lratCheckerSound f1528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1528
  · intro a ha; simp [p1528] at ha; subst a; trivial
  · exact checked1528
theorem derived1528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1528 := by
  apply localUnsat_implies_entails f1528 [c1509, c106, c1485, c1512, c105, c1516, c1518, c1527, c1318, c4, c1524, c1525, c1496, c1510, c194, c165, c168, c509, c188, c80, c234, c255] c1528 unsat1528 (by rfl) a
  have h0 : Entails.eval a c1509 := derived1509 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1512 := derived1512 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1516 := derived1516 a h
  have h6 : Entails.eval a c1518 := derived1518 a h
  have h7 : Entails.eval a c1527 := derived1527 a h
  have h8 : Entails.eval a c1318 := derived1318 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c1524 := derived1524 a h
  have h11 : Entails.eval a c1525 := derived1525 a h
  have h12 : Entails.eval a c1496 := derived1496 a h
  have h13 : Entails.eval a c1510 := derived1510 a h
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c509 := derived509 a h
  have h18 : Entails.eval a c188 := h 187 (by decide)
  have h19 : Entails.eval a c80 := h 79 (by decide)
  have h20 : Entails.eval a c234 := h 233 (by decide)
  have h21 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1529 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c7, some c117, some c1510, some c33, some c251, some c256, some c8, some c943, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1529 : lratChecker f1529 p1529 = .success := by decide +kernel
theorem unsat1529 : Unsatisfiable (PosFin 57) f1529 := by
  apply lratCheckerSound f1529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1529
  · intro a ha; simp [p1529] at ha; subst a; trivial
  · exact checked1529
theorem derived1529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1529 := by
  apply localUnsat_implies_entails f1529 [c13, c7, c117, c1510, c33, c251, c256, c8, c943] c1529 unsat1529 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c1510 := derived1510 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c943 := derived943 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1530 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1528, some c1529, some c105, some c1516, some c1003, some c122, some c32, some c25, some c117, some c170, some c2, some c1491, some c248, some c245, some c103, some c80, some c376, some c357, some c164, some c179, some c1496, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1530 : lratChecker f1530 p1530 = .success := by decide +kernel
theorem unsat1530 : Unsatisfiable (PosFin 57) f1530 := by
  apply lratCheckerSound f1530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1530
  · intro a ha; simp [p1530] at ha; subst a; trivial
  · exact checked1530
theorem derived1530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1530 := by
  apply localUnsat_implies_entails f1530 [c1485, c1509, c106, c1528, c1529, c105, c1516, c1003, c122, c32, c25, c117, c170, c2, c1491, c248, c245, c103, c80, c376, c357, c164, c179, c1496] c1530 unsat1530 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1528 := derived1528 a h
  have h4 : Entails.eval a c1529 := derived1529 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c1491 := derived1491 a h
  have h15 : Entails.eval a c248 := h 247 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c376 := h 375 (by decide)
  have h20 : Entails.eval a c357 := h 356 (by decide)
  have h21 : Entails.eval a c164 := h 163 (by decide)
  have h22 : Entails.eval a c179 := h 178 (by decide)
  have h23 : Entails.eval a c1496 := derived1496 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1531 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c379, some c96, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1531 : lratChecker f1531 p1531 = .success := by decide +kernel
theorem unsat1531 : Unsatisfiable (PosFin 57) f1531 := by
  apply lratCheckerSound f1531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1531
  · intro a ha; simp [p1531] at ha; subst a; trivial
  · exact checked1531
theorem derived1531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1531 := by
  apply localUnsat_implies_entails f1531 [c382, c379, c96] c1531 unsat1531 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1532 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c19, some c122, some c32, some c117, some c248, some c2, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1532 : lratChecker f1532 p1532 = .success := by decide +kernel
theorem unsat1532 : Unsatisfiable (PosFin 57) f1532 := by
  apply lratCheckerSound f1532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1532
  · intro a ha; simp [p1532] at ha; subst a; trivial
  · exact checked1532
theorem derived1532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1532 := by
  apply localUnsat_implies_entails f1532 [c8, c19, c122, c32, c117, c248, c2] c1532 unsat1532 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1533 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1528, some c1529, some c105, some c1532, some c1516, some c1530, some c184, some c1517, some c117, some c1510, some c194, some c32, some c188, some c1330, some c264, some c380, some c255, some c377, some c518, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1533 : lratChecker f1533 p1533 = .success := by decide +kernel
theorem unsat1533 : Unsatisfiable (PosFin 57) f1533 := by
  apply lratCheckerSound f1533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1533
  · intro a ha; simp [p1533] at ha; subst a; trivial
  · exact checked1533
theorem derived1533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1533 := by
  apply localUnsat_implies_entails f1533 [c1485, c1509, c106, c1528, c1529, c105, c1532, c1516, c1530, c184, c1517, c117, c1510, c194, c32, c188, c1330, c264, c380, c255, c377, c518] c1533 unsat1533 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1528 := derived1528 a h
  have h4 : Entails.eval a c1529 := derived1529 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1532 := derived1532 a h
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c1530 := derived1530 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c1517 := derived1517 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c1510 := derived1510 a h
  have h13 : Entails.eval a c194 := h 193 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c1330 := derived1330 a h
  have h17 : Entails.eval a c264 := h 263 (by decide)
  have h18 : Entails.eval a c380 := h 379 (by decide)
  have h19 : Entails.eval a c255 := h 254 (by decide)
  have h20 : Entails.eval a c377 := h 376 (by decide)
  have h21 : Entails.eval a c518 := derived518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1534 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1509, some c106, some c1485, some c1528, some c1529, some c105, some c1516, some c1530, some c184, some c1532, some c1533, some c80, some c619, some c122, some c32, some c117, some c2, some c1496, some c380, some c190, some c188, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1534 : lratChecker f1534 p1534 = .success := by decide +kernel
theorem unsat1534 : Unsatisfiable (PosFin 57) f1534 := by
  apply lratCheckerSound f1534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1534
  · intro a ha; simp [p1534] at ha; subst a; trivial
  · exact checked1534
theorem derived1534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1534 := by
  apply localUnsat_implies_entails f1534 [c1509, c106, c1485, c1528, c1529, c105, c1516, c1530, c184, c1532, c1533, c80, c619, c122, c32, c117, c2, c1496, c380, c190, c188] c1534 unsat1534 (by rfl) a
  have h0 : Entails.eval a c1509 := derived1509 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1528 := derived1528 a h
  have h4 : Entails.eval a c1529 := derived1529 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c1530 := derived1530 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c1532 := derived1532 a h
  have h10 : Entails.eval a c1533 := derived1533 a h
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c619 := derived619 a h
  have h13 : Entails.eval a c122 := h 121 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c1496 := derived1496 a h
  have h18 : Entails.eval a c380 := h 379 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1535 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨55, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c8, some c594, some c347, some c135, some c308, some c145, some c211, some c49, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1535 : lratChecker f1535 p1535 = .success := by decide +kernel
theorem unsat1535 : Unsatisfiable (PosFin 57) f1535 := by
  apply lratCheckerSound f1535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1535
  · intro a ha; simp [p1535] at ha; subst a; trivial
  · exact checked1535
theorem derived1535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1535 := by
  apply localUnsat_implies_entails f1535 [c35, c8, c594, c347, c135, c308, c145, c211, c49] c1535 unsat1535 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c594 := derived594 a h
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c211 := h 210 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1536 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c179, some c379, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1536 : lratChecker f1536 p1536 = .success := by decide +kernel
theorem unsat1536 : Unsatisfiable (PosFin 57) f1536 := by
  apply lratCheckerSound f1536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1536
  · intro a ha; simp [p1536] at ha; subst a; trivial
  · exact checked1536
theorem derived1536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1536 := by
  apply localUnsat_implies_entails f1536 [c357, c179, c379] c1536 unsat1536 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1537 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c1003, some c13, some c192, some c1341, some c28, some c35, some c111, some c39, some c1535, some c168, some c74, some c85, some c84, some c370, some c170, some c230, some c113, some c1536, some c378, some c376, some c103, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1537 : lratChecker f1537 p1537 = .success := by decide +kernel
theorem unsat1537 : Unsatisfiable (PosFin 57) f1537 := by
  apply lratCheckerSound f1537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1537
  · intro a ha; simp [p1537] at ha; subst a; trivial
  · exact checked1537
theorem derived1537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1537 := by
  apply localUnsat_implies_entails f1537 [c7, c1003, c13, c192, c1341, c28, c35, c111, c39, c1535, c168, c74, c85, c84, c370, c170, c230, c113, c1536, c378, c376, c103] c1537 unsat1537 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c1341 := derived1341 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c1535 := derived1535 a h
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c1536 := derived1536 a h
  have h19 : Entails.eval a c378 := h 377 (by decide)
  have h20 : Entails.eval a c376 := h 375 (by decide)
  have h21 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1538 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c1341, some c7, some c1003, some c1537, some c117, some c122, some c22, some c33, some c32, some c165, some c251, some c111, some c75, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1538 : lratChecker f1538 p1538 = .success := by decide +kernel
theorem unsat1538 : Unsatisfiable (PosFin 57) f1538 := by
  apply lratCheckerSound f1538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1538
  · intro a ha; simp [p1538] at ha; subst a; trivial
  · exact checked1538
theorem derived1538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1538 := by
  apply localUnsat_implies_entails f1538 [c13, c1341, c7, c1003, c1537, c117, c122, c22, c33, c32, c165, c251, c111, c75] c1538 unsat1538 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c1341 := derived1341 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1537 := derived1537 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1539 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c1516, some c1538, some c1003, some c122, some c35, some c1527, some c37, some c4, some c252, some c1531, some c447, some c96, some c103, some c1034, some c378, some c741, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1539 : lratChecker f1539 p1539 = .success := by decide +kernel
theorem unsat1539 : Unsatisfiable (PosFin 57) f1539 := by
  apply lratCheckerSound f1539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1539
  · intro a ha; simp [p1539] at ha; subst a; trivial
  · exact checked1539
theorem derived1539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1539 := by
  apply localUnsat_implies_entails f1539 [c39, c1516, c1538, c1003, c122, c35, c1527, c37, c4, c252, c1531, c447, c96, c103, c1034, c378, c741] c1539 unsat1539 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c1516 := derived1516 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c1527 := derived1527 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c1531 := derived1531 a h
  have h11 : Entails.eval a c447 := derived447 a h
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c1034 := derived1034 a h
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c741 := derived741 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1540 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1534, some c1538, some c105, some c1516, some c1539, some c184, some c39, some c1318, some c37, some c252, some c96, some c103, some c1034, some c1517, some c188, some c1278, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1540 : lratChecker f1540 p1540 = .success := by decide +kernel
theorem unsat1540 : Unsatisfiable (PosFin 57) f1540 := by
  apply lratCheckerSound f1540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1540
  · intro a ha; simp [p1540] at ha; subst a; trivial
  · exact checked1540
theorem derived1540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1540 := by
  apply localUnsat_implies_entails f1540 [c1485, c1509, c106, c1534, c1538, c105, c1516, c1539, c184, c39, c1318, c37, c252, c96, c103, c1034, c1517, c188, c1278] c1540 unsat1540 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1534 := derived1534 a h
  have h4 : Entails.eval a c1538 := derived1538 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1516 := derived1516 a h
  have h7 : Entails.eval a c1539 := derived1539 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c1318 := derived1318 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c1034 := derived1034 a h
  have h16 : Entails.eval a c1517 := derived1517 a h
  have h17 : Entails.eval a c188 := h 187 (by decide)
  have h18 : Entails.eval a c1278 := derived1278 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1541 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c1527, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1541 : lratChecker f1541 p1541 = .success := by decide +kernel
theorem unsat1541 : Unsatisfiable (PosFin 57) f1541 := by
  apply lratCheckerSound f1541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1541
  · intro a ha; simp [p1541] at ha; subst a; trivial
  · exact checked1541
theorem derived1541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1541 := by
  apply localUnsat_implies_entails f1541 [c35, c1527] c1541 unsat1541 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c1527 := derived1527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1542 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1509, some c106, some c1485, some c1534, some c28, some c1538, some c105, some c1516, some c39, some c1540, some c1541, some c122, some c19, some c619, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1542 : lratChecker f1542 p1542 = .success := by decide +kernel
theorem unsat1542 : Unsatisfiable (PosFin 57) f1542 := by
  apply lratCheckerSound f1542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1542
  · intro a ha; simp [p1542] at ha; subst a; trivial
  · exact checked1542
theorem derived1542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1542 := by
  apply localUnsat_implies_entails f1542 [c1509, c106, c1485, c1534, c28, c1538, c105, c1516, c39, c1540, c1541, c122, c19, c619] c1542 unsat1542 (by rfl) a
  have h0 : Entails.eval a c1509 := derived1509 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1534 := derived1534 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1538 := derived1538 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c1540 := derived1540 a h
  have h10 : Entails.eval a c1541 := derived1541 a h
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c619 := derived619 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1543 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨55, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1510, some c120, some c168, some c33, some c80, some c256, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1543 : lratChecker f1543 p1543 = .success := by decide +kernel
theorem unsat1543 : Unsatisfiable (PosFin 57) f1543 := by
  apply lratCheckerSound f1543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1543
  · intro a ha; simp [p1543] at ha; subst a; trivial
  · exact checked1543
theorem derived1543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1543 := by
  apply localUnsat_implies_entails f1543 [c1510, c120, c168, c33, c80, c256] c1543 unsat1543 (by rfl) a
  have h0 : Entails.eval a c1510 := derived1510 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1544 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨20, by decide⟩, false), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨47, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c25, some c370, some c443, some c252, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1544 : lratChecker f1544 p1544 = .success := by decide +kernel
theorem unsat1544 : Unsatisfiable (PosFin 57) f1544 := by
  apply lratCheckerSound f1544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1544
  · intro a ha; simp [p1544] at ha; subst a; trivial
  · exact checked1544
theorem derived1544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1544 := by
  apply localUnsat_implies_entails f1544 [c91, c25, c370, c443, c252] c1544 unsat1544 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c443 := derived443 a h
  have h4 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1545 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c7, some c1510, some c1543, some c8, some c1263, some c15, some c256, some c589, some c378, some c193, some c1278, some c167, some c111, some c33, some c27, some c248, some c96, some c383, some c669, some c1544, some c361, some c375, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1545 : lratChecker f1545 p1545 = .success := by decide +kernel
theorem unsat1545 : Unsatisfiable (PosFin 57) f1545 := by
  apply lratCheckerSound f1545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1545
  · intro a ha; simp [p1545] at ha; subst a; trivial
  · exact checked1545
theorem derived1545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1545 := by
  apply localUnsat_implies_entails f1545 [c13, c7, c1510, c1543, c8, c1263, c15, c256, c589, c378, c193, c1278, c167, c111, c33, c27, c248, c96, c383, c669, c1544, c361, c375] c1545 unsat1545 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c1510 := derived1510 a h
  have h3 : Entails.eval a c1543 := derived1543 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c1263 := derived1263 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c1278 := derived1278 a h
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c383 := h 382 (by decide)
  have h19 : Entails.eval a c669 := derived669 a h
  have h20 : Entails.eval a c1544 := derived1544 a h
  have h21 : Entails.eval a c361 := h 360 (by decide)
  have h22 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1546 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c17, some c1527, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1546 : lratChecker f1546 p1546 = .success := by decide +kernel
theorem unsat1546 : Unsatisfiable (PosFin 57) f1546 := by
  apply lratCheckerSound f1546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1546
  · intro a ha; simp [p1546] at ha; subst a; trivial
  · exact checked1546
theorem derived1546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1546 := by
  apply localUnsat_implies_entails f1546 [c15, c17, c1527] c1546 unsat1546 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c1527 := derived1527 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1547 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c23, some c3, some c383, some c1531, some c77, some c103, some c374, some c378, some c358, some c179, some c161, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1547 : lratChecker f1547 p1547 = .success := by decide +kernel
theorem unsat1547 : Unsatisfiable (PosFin 57) f1547 := by
  apply lratCheckerSound f1547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1547
  · intro a ha; simp [p1547] at ha; subst a; trivial
  · exact checked1547
theorem derived1547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1547 := by
  apply localUnsat_implies_entails f1547 [c1003, c23, c3, c383, c1531, c77, c103, c374, c378, c358, c179, c161] c1547 unsat1547 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c1531 := derived1531 a h
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1548 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1546, some c1547, some c1527, some c4, some c1531, some c1524, some c634, some c178, some c256, some c376, some c103, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1548 : lratChecker f1548 p1548 = .success := by decide +kernel
theorem unsat1548 : Unsatisfiable (PosFin 57) f1548 := by
  apply lratCheckerSound f1548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1548
  · intro a ha; simp [p1548] at ha; subst a; trivial
  · exact checked1548
theorem derived1548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1548 := by
  apply localUnsat_implies_entails f1548 [c1485, c1509, c106, c1542, c1545, c105, c1546, c1547, c1527, c4, c1531, c1524, c634, c178, c256, c376, c103] c1548 unsat1548 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1542 := derived1542 a h
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1546 := derived1546 a h
  have h7 : Entails.eval a c1547 := derived1547 a h
  have h8 : Entails.eval a c1527 := derived1527 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c1531 := derived1531 a h
  have h11 : Entails.eval a c1524 := derived1524 a h
  have h12 : Entails.eval a c634 := derived634 a h
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1549 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c23, some c3, some c383, some c96, some c77, some c103, some c248, some c172, some c375, some c256, some c32, some c236, some c124, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1549 : lratChecker f1549 p1549 = .success := by decide +kernel
theorem unsat1549 : Unsatisfiable (PosFin 57) f1549 := by
  apply lratCheckerSound f1549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1549
  · intro a ha; simp [p1549] at ha; subst a; trivial
  · exact checked1549
theorem derived1549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1549 := by
  apply localUnsat_implies_entails f1549 [c1003, c23, c3, c383, c96, c77, c103, c248, c172, c375, c256, c32, c236, c124] c1549 unsat1549 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1550 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1263, some c193, some c2, some c1491, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1550 : lratChecker f1550 p1550 = .success := by decide +kernel
theorem unsat1550 : Unsatisfiable (PosFin 57) f1550 := by
  apply lratCheckerSound f1550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1550
  · intro a ha; simp [p1550] at ha; subst a; trivial
  · exact checked1550
theorem derived1550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1550 := by
  apply localUnsat_implies_entails f1550 [c1263, c193, c2, c1491] c1550 unsat1550 (by rfl) a
  have h0 : Entails.eval a c1263 := derived1263 a h
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1491 := derived1491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1551 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c105, some c1485, some c256, some c589, some c378, some c634, some c190, some c182, some c705, some c1531, some c77, some c512, some c172, some c358, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1551 : lratChecker f1551 p1551 = .success := by decide +kernel
theorem unsat1551 : Unsatisfiable (PosFin 57) f1551 := by
  apply lratCheckerSound f1551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1551
  · intro a ha; simp [p1551] at ha; subst a; trivial
  · exact checked1551
theorem derived1551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1551 := by
  apply localUnsat_implies_entails f1551 [c1003, c105, c1485, c256, c589, c378, c634, c190, c182, c705, c1531, c77, c512, c172, c358] c1551 unsat1551 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c634 := derived634 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c705 := derived705 a h
  have h10 : Entails.eval a c1531 := derived1531 a h
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c512 := derived512 a h
  have h13 : Entails.eval a c172 := h 171 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1552 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1052, some c51, some c135, some c67, some c59, some c218, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1552 : lratChecker f1552 p1552 = .success := by decide +kernel
theorem unsat1552 : Unsatisfiable (PosFin 57) f1552 := by
  apply lratCheckerSound f1552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1552
  · intro a ha; simp [p1552] at ha; subst a; trivial
  · exact checked1552
theorem derived1552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1552 := by
  apply localUnsat_implies_entails f1552 [c1052, c51, c135, c67, c59, c218] c1552 unsat1552 (by rfl) a
  have h0 : Entails.eval a c1052 := derived1052 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1553 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1548, some c1549, some c1550, some c1551, some c103, some c383, some c376, some c178, some c116, some c1552, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1553 : lratChecker f1553 p1553 = .success := by decide +kernel
theorem unsat1553 : Unsatisfiable (PosFin 57) f1553 := by
  apply lratCheckerSound f1553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1553
  · intro a ha; simp [p1553] at ha; subst a; trivial
  · exact checked1553
theorem derived1553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1553 := by
  apply localUnsat_implies_entails f1553 [c1485, c1509, c106, c1542, c1545, c105, c1548, c1549, c1550, c1551, c103, c383, c376, c178, c116, c1552] c1553 unsat1553 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1542 := derived1542 a h
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1548 := derived1548 a h
  have h7 : Entails.eval a c1549 := derived1549 a h
  have h8 : Entails.eval a c1550 := derived1550 a h
  have h9 : Entails.eval a c1551 := derived1551 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c383 := h 382 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c1552 := derived1552 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1554 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1553, some c1003, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c15, some c3, some c383, some c251, some c1531, some c96, some c103, some c4, some c248, some c378, some c22, some c32, some c179, some c263, some c113, some c190, some c512, some c677, some c231, some c59, some c217, some c219, some c321, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1554 : lratChecker f1554 p1554 = .success := by decide +kernel
theorem unsat1554 : Unsatisfiable (PosFin 57) f1554 := by
  apply lratCheckerSound f1554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1554
  · intro a ha; simp [p1554] at ha; subst a; trivial
  · exact checked1554
theorem derived1554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1554 := by
  apply localUnsat_implies_entails f1554 [c1553, c1003, c1485, c1509, c106, c1542, c1545, c105, c15, c3, c383, c251, c1531, c96, c103, c4, c248, c378, c22, c32, c179, c263, c113, c190, c512, c677, c231, c59, c217, c219, c321] c1554 unsat1554 (by rfl) a
  have h0 : Entails.eval a c1553 := derived1553 a h
  have h1 : Entails.eval a c1003 := derived1003 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1542 := derived1542 a h
  have h6 : Entails.eval a c1545 := derived1545 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c1531 := derived1531 a h
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c378 := h 377 (by decide)
  have h18 : Entails.eval a c22 := h 21 (by decide)
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c179 := h 178 (by decide)
  have h21 : Entails.eval a c263 := h 262 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c190 := h 189 (by decide)
  have h24 : Entails.eval a c512 := derived512 a h
  have h25 : Entails.eval a c677 := derived677 a h
  have h26 : Entails.eval a c231 := h 230 (by decide)
  have h27 : Entails.eval a c59 := h 58 (by decide)
  have h28 : Entails.eval a c217 := h 216 (by decide)
  have h29 : Entails.eval a c219 := h 218 (by decide)
  have h30 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1555 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c8, some c17, some c256, some c1203, some c1245, some c260, some c32, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1555 : lratChecker f1555 p1555 = .success := by decide +kernel
theorem unsat1555 : Unsatisfiable (PosFin 57) f1555 := by
  apply lratCheckerSound f1555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1555
  · intro a ha; simp [p1555] at ha; subst a; trivial
  · exact checked1555
theorem derived1555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1555 := by
  apply localUnsat_implies_entails f1555 [c1003, c8, c17, c256, c1203, c1245, c260, c32] c1555 unsat1555 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c1203 := derived1203 a h
  have h5 : Entails.eval a c1245 := derived1245 a h
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1556 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c105, some c1485, some c256, some c589, some c634, some c190, some c182, some c705, some c1531, some c96, some c4, some c248, some c1245, some c32, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1556 : lratChecker f1556 p1556 = .success := by decide +kernel
theorem unsat1556 : Unsatisfiable (PosFin 57) f1556 := by
  apply lratCheckerSound f1556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1556
  · intro a ha; simp [p1556] at ha; subst a; trivial
  · exact checked1556
theorem derived1556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1556 := by
  apply localUnsat_implies_entails f1556 [c1003, c105, c1485, c256, c589, c634, c190, c182, c705, c1531, c96, c4, c248, c1245, c32] c1556 unsat1556 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c634 := derived634 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c705 := derived705 a h
  have h9 : Entails.eval a c1531 := derived1531 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c1245 := derived1245 a h
  have h14 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1557 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1526, some c131, some c65, some c67, some c156, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1557 : lratChecker f1557 p1557 = .success := by decide +kernel
theorem unsat1557 : Unsatisfiable (PosFin 57) f1557 := by
  apply lratCheckerSound f1557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1557
  · intro a ha; simp [p1557] at ha; subst a; trivial
  · exact checked1557
theorem derived1557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1557 := by
  apply localUnsat_implies_entails f1557 [c1526, c131, c65, c67, c156] c1557 unsat1557 (by rfl) a
  have h0 : Entails.eval a c1526 := derived1526 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1558 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1553, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1554, some c1555, some c1556, some c103, some c80, some c383, some c376, some c178, some c190, some c182, some c1557, some c1034, some c74, some c2, some c168, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1558 : lratChecker f1558 p1558 = .success := by decide +kernel
theorem unsat1558 : Unsatisfiable (PosFin 57) f1558 := by
  apply lratCheckerSound f1558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1558
  · intro a ha; simp [p1558] at ha; subst a; trivial
  · exact checked1558
theorem derived1558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1558 := by
  apply localUnsat_implies_entails f1558 [c1553, c1485, c1509, c106, c1542, c1545, c105, c1554, c1555, c1556, c103, c80, c383, c376, c178, c190, c182, c1557, c1034, c74, c2, c168] c1558 unsat1558 (by rfl) a
  have h0 : Entails.eval a c1553 := derived1553 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1542 := derived1542 a h
  have h5 : Entails.eval a c1545 := derived1545 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1554 := derived1554 a h
  have h8 : Entails.eval a c1555 := derived1555 a h
  have h9 : Entails.eval a c1556 := derived1556 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c376 := h 375 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c1557 := derived1557 a h
  have h18 : Entails.eval a c1034 := derived1034 a h
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c2 := h 1 (by decide)
  have h21 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1559 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1003, some c383, some c251, some c1531, some c96, some c77, some c103, some c248, some c172, some c378, some c32, some c358, some c124, some c368, some c236, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1559 : lratChecker f1559 p1559 = .success := by decide +kernel
theorem unsat1559 : Unsatisfiable (PosFin 57) f1559 := by
  apply lratCheckerSound f1559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1559
  · intro a ha; simp [p1559] at ha; subst a; trivial
  · exact checked1559
theorem derived1559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1559 := by
  apply localUnsat_implies_entails f1559 [c1003, c383, c251, c1531, c96, c77, c103, c248, c172, c378, c32, c358, c124, c368, c236] c1559 unsat1559 (by rfl) a
  have h0 : Entails.eval a c1003 := derived1003 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c1531 := derived1531 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c172 := h 171 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1560 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c25, some c260, some c683, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1560 : lratChecker f1560 p1560 = .success := by decide +kernel
theorem unsat1560 : Unsatisfiable (PosFin 57) f1560 := by
  apply lratCheckerSound f1560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1560
  · intro a ha; simp [p1560] at ha; subst a; trivial
  · exact checked1560
theorem derived1560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1560 := by
  apply localUnsat_implies_entails f1560 [c32, c25, c260, c683] c1560 unsat1560 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1561 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1003, some c1553, some c1558, some c1550, some c1559, some c3, some c1551, some c103, some c80, some c376, some c178, some c116, some c164, some c357, some c1560, some c124, some c231, some c683, some c371, some c84, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1561 : lratChecker f1561 p1561 = .success := by decide +kernel
theorem unsat1561 : Unsatisfiable (PosFin 57) f1561 := by
  apply lratCheckerSound f1561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1561
  · intro a ha; simp [p1561] at ha; subst a; trivial
  · exact checked1561
theorem derived1561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1561 := by
  apply localUnsat_implies_entails f1561 [c1485, c1509, c106, c1542, c1545, c105, c1003, c1553, c1558, c1550, c1559, c3, c1551, c103, c80, c376, c178, c116, c164, c357, c1560, c124, c231, c683, c371, c84] c1561 unsat1561 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1542 := derived1542 a h
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c1553 := derived1553 a h
  have h8 : Entails.eval a c1558 := derived1558 a h
  have h9 : Entails.eval a c1550 := derived1550 a h
  have h10 : Entails.eval a c1559 := derived1559 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c1551 := derived1551 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c178 := h 177 (by decide)
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  have h20 : Entails.eval a c1560 := derived1560 a h
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c231 := h 230 (by decide)
  have h23 : Entails.eval a c683 := derived683 a h
  have h24 : Entails.eval a c371 := h 370 (by decide)
  have h25 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1562 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1546, some c184, some c1531, some c3, some c1552, some c1524, some c259, some c634, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1562 : lratChecker f1562 p1562 = .success := by decide +kernel
theorem unsat1562 : Unsatisfiable (PosFin 57) f1562 := by
  apply lratCheckerSound f1562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1562
  · intro a ha; simp [p1562] at ha; subst a; trivial
  · exact checked1562
theorem derived1562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1562 := by
  apply localUnsat_implies_entails f1562 [c1561, c1485, c1509, c106, c1542, c1545, c105, c1546, c184, c1531, c3, c1552, c1524, c259, c634] c1562 unsat1562 (by rfl) a
  have h0 : Entails.eval a c1561 := derived1561 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1542 := derived1542 a h
  have h5 : Entails.eval a c1545 := derived1545 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1546 := derived1546 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c1531 := derived1531 a h
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c1552 := derived1552 a h
  have h12 : Entails.eval a c1524 := derived1524 a h
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c634 := derived634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1563 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c77, some c172, some c375, some c363, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1563 : lratChecker f1563 p1563 = .success := by decide +kernel
theorem unsat1563 : Unsatisfiable (PosFin 57) f1563 := by
  apply lratCheckerSound f1563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1563
  · intro a ha; simp [p1563] at ha; subst a; trivial
  · exact checked1563
theorem derived1563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1563 := by
  apply localUnsat_implies_entails f1563 [c5, c77, c172, c375, c363] c1563 unsat1563 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1564 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c74, some c2, some c166, some c168, some c706, some c363, some c1143, some c368, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1564 : lratChecker f1564 p1564 = .success := by decide +kernel
theorem unsat1564 : Unsatisfiable (PosFin 57) f1564 := by
  apply lratCheckerSound f1564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1564
  · intro a ha; simp [p1564] at ha; subst a; trivial
  · exact checked1564
theorem derived1564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1564 := by
  apply localUnsat_implies_entails f1564 [c1485, c74, c2, c166, c168, c706, c363, c1143, c368] c1564 unsat1564 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c706 := derived706 a h
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c1143 := derived1143 a h
  have h8 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1565 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨43, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c1485, some c1564, some c248, some c381, some c22, some c32, some c371, some c363, some c358, some c702, some c370, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1565 : lratChecker f1565 p1565 = .success := by decide +kernel
theorem unsat1565 : Unsatisfiable (PosFin 57) f1565 := by
  apply lratCheckerSound f1565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1565
  · intro a ha; simp [p1565] at ha; subst a; trivial
  · exact checked1565
theorem derived1565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1565 := by
  apply localUnsat_implies_entails f1565 [c105, c1485, c1564, c248, c381, c22, c32, c371, c363, c358, c702, c370] c1565 unsat1565 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c702 := derived702 a h
  have h11 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1566 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨51, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c2, some c1542, some c1509, some c1320, some c297, some c138, some c210, some c42, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1566 : lratChecker f1566 p1566 = .success := by decide +kernel
theorem unsat1566 : Unsatisfiable (PosFin 57) f1566 := by
  apply lratCheckerSound f1566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1566
  · intro a ha; simp [p1566] at ha; subst a; trivial
  · exact checked1566
theorem derived1566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1566 := by
  apply localUnsat_implies_entails f1566 [c1485, c2, c1542, c1509, c1320, c297, c138, c210, c42] c1566 unsat1566 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c1542 := derived1542 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c1320 := derived1320 a h
  have h5 : Entails.eval a c297 := h 296 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1567 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1542, some c3, some c1509, some c106, some c15, some c1485, some c1545, some c194, some c127, some c1566, some c190, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1567 : lratChecker f1567 p1567 = .success := by decide +kernel
theorem unsat1567 : Unsatisfiable (PosFin 57) f1567 := by
  apply lratCheckerSound f1567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1567
  · intro a ha; simp [p1567] at ha; subst a; trivial
  · exact checked1567
theorem derived1567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1567 := by
  apply localUnsat_implies_entails f1567 [c1542, c3, c1509, c106, c15, c1485, c1545, c194, c127, c1566, c190] c1567 unsat1567 (by rfl) a
  have h0 : Entails.eval a c1542 := derived1542 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1485 := derived1485 a h
  have h6 : Entails.eval a c1545 := derived1545 a h
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c1566 := derived1566 a h
  have h10 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1568 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨43, by decide⟩, false), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1565, some c377, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1568 : lratChecker f1568 p1568 = .success := by decide +kernel
theorem unsat1568 : Unsatisfiable (PosFin 57) f1568 := by
  apply lratCheckerSound f1568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1568
  · intro a ha; simp [p1568] at ha; subst a; trivial
  · exact checked1568
theorem derived1568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1568 := by
  apply localUnsat_implies_entails f1568 [c1565, c377] c1568 unsat1568 (by rfl) a
  have h0 : Entails.eval a c1565 := derived1565 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1569 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c374, some c84, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1569 : lratChecker f1569 p1569 = .success := by decide +kernel
theorem unsat1569 : Unsatisfiable (PosFin 57) f1569 := by
  apply lratCheckerSound f1569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1569
  · intro a ha; simp [p1569] at ha; subst a; trivial
  · exact checked1569
theorem derived1569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1569 := by
  apply localUnsat_implies_entails f1569 [c371, c374, c84] c1569 unsat1569 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1570 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1562, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c23, some c15, some c3, some c1531, some c1563, some c1567, some c188, some c1568, some c80, some c1569, some c363, some c375, some c370, some c84, some c25, some c358, some c1233, some c241, some c12, some c231, some c124, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1570 : lratChecker f1570 p1570 = .success := by decide +kernel
theorem unsat1570 : Unsatisfiable (PosFin 57) f1570 := by
  apply lratCheckerSound f1570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1570
  · intro a ha; simp [p1570] at ha; subst a; trivial
  · exact checked1570
theorem derived1570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1570 := by
  apply localUnsat_implies_entails f1570 [c1562, c1561, c1485, c1509, c106, c1542, c1545, c105, c23, c15, c3, c1531, c1563, c1567, c188, c1568, c80, c1569, c363, c375, c370, c84, c25, c358, c1233, c241, c12, c231, c124] c1570 unsat1570 (by rfl) a
  have h0 : Entails.eval a c1562 := derived1562 a h
  have h1 : Entails.eval a c1561 := derived1561 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1542 := derived1542 a h
  have h6 : Entails.eval a c1545 := derived1545 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c1531 := derived1531 a h
  have h12 : Entails.eval a c1563 := derived1563 a h
  have h13 : Entails.eval a c1567 := derived1567 a h
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c1568 := derived1568 a h
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c1569 := derived1569 a h
  have h18 : Entails.eval a c363 := h 362 (by decide)
  have h19 : Entails.eval a c375 := h 374 (by decide)
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c25 := h 24 (by decide)
  have h23 : Entails.eval a c358 := h 357 (by decide)
  have h24 : Entails.eval a c1233 := derived1233 a h
  have h25 : Entails.eval a c241 := h 240 (by decide)
  have h26 : Entails.eval a c12 := h 11 (by decide)
  have h27 : Entails.eval a c231 := h 230 (by decide)
  have h28 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1571 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c1562, some c1570, some c1552, some c259, some c634, some c116, some c8, some c19, some c113, some c32, some c25, some c248, some c172, some c2, some c118, some c1203, some c24, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1571 : lratChecker f1571 p1571 = .success := by decide +kernel
theorem unsat1571 : Unsatisfiable (PosFin 57) f1571 := by
  apply lratCheckerSound f1571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1571
  · intro a ha; simp [p1571] at ha; subst a; trivial
  · exact checked1571
theorem derived1571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1571 := by
  apply localUnsat_implies_entails f1571 [c1485, c1509, c106, c1542, c1545, c105, c1562, c1570, c1552, c259, c634, c116, c8, c19, c113, c32, c25, c248, c172, c2, c118, c1203, c24] c1571 unsat1571 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1542 := derived1542 a h
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1562 := derived1562 a h
  have h7 : Entails.eval a c1570 := derived1570 a h
  have h8 : Entails.eval a c1552 := derived1552 a h
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c634 := derived634 a h
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c1203 := derived1203 a h
  have h22 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1572 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨56, by decide⟩, false), (⟨12, by decide⟩, false), (⟨51, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c105, some c1531, some c106, some c1565, some c1564, some c87, some c248, some c381, some c22, some c32, some c168, some c263, some c250, some c12, some c77, some c644, some c652, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1572 : lratChecker f1572 p1572 = .success := by decide +kernel
theorem unsat1572 : Unsatisfiable (PosFin 57) f1572 := by
  apply lratCheckerSound f1572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1572
  · intro a ha; simp [p1572] at ha; subst a; trivial
  · exact checked1572
theorem derived1572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1572 := by
  apply localUnsat_implies_entails f1572 [c1485, c105, c1531, c106, c1565, c1564, c87, c248, c381, c22, c32, c168, c263, c250, c12, c77, c644, c652] c1572 unsat1572 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1531 := derived1531 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1565 := derived1565 a h
  have h5 : Entails.eval a c1564 := derived1564 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c77 := h 76 (by decide)
  have h16 : Entails.eval a c644 := derived644 a h
  have h17 : Entails.eval a c652 := derived652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1573 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c3, some c1531, some c184, some c15, some c1571, some c1572, some c377, some c188, some c194, some c190, some c127, some c2, some c1320, some c248, some c297, some c32, some c138, some c263, some c264, some c43, some c1364, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1573 : lratChecker f1573 p1573 = .success := by decide +kernel
theorem unsat1573 : Unsatisfiable (PosFin 57) f1573 := by
  apply lratCheckerSound f1573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1573
  · intro a ha; simp [p1573] at ha; subst a; trivial
  · exact checked1573
theorem derived1573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1573 := by
  apply localUnsat_implies_entails f1573 [c1561, c1485, c1509, c106, c1542, c1545, c105, c3, c1531, c184, c15, c1571, c1572, c377, c188, c194, c190, c127, c2, c1320, c248, c297, c32, c138, c263, c264, c43, c1364] c1573 unsat1573 (by rfl) a
  have h0 : Entails.eval a c1561 := derived1561 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1542 := derived1542 a h
  have h5 : Entails.eval a c1545 := derived1545 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1531 := derived1531 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c1571 := derived1571 a h
  have h12 : Entails.eval a c1572 := derived1572 a h
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c1320 := derived1320 a h
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c32 := h 31 (by decide)
  have h23 : Entails.eval a c138 := h 137 (by decide)
  have h24 : Entails.eval a c263 := h 262 (by decide)
  have h25 : Entails.eval a c264 := h 263 (by decide)
  have h26 : Entails.eval a c43 := h 42 (by decide)
  have h27 : Entails.eval a c1364 := derived1364 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1574 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1571, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c15, some c3, some c1573, some c103, some c250, some c32, some c120, some c245, some c2, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1574 : lratChecker f1574 p1574 = .success := by decide +kernel
theorem unsat1574 : Unsatisfiable (PosFin 57) f1574 := by
  apply lratCheckerSound f1574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1574
  · intro a ha; simp [p1574] at ha; subst a; trivial
  · exact checked1574
theorem derived1574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1574 := by
  apply localUnsat_implies_entails f1574 [c1571, c1485, c1509, c106, c1542, c1545, c105, c15, c3, c1573, c103, c250, c32, c120, c245, c2] c1574 unsat1574 (by rfl) a
  have h0 : Entails.eval a c1571 := derived1571 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1542 := derived1542 a h
  have h5 : Entails.eval a c1545 := derived1545 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c1573 := derived1573 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1575 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1557, some c17, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1575 : lratChecker f1575 p1575 = .success := by decide +kernel
theorem unsat1575 : Unsatisfiable (PosFin 57) f1575 := by
  apply lratCheckerSound f1575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1575
  · intro a ha; simp [p1575] at ha; subst a; trivial
  · exact checked1575
theorem derived1575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1575 := by
  apply localUnsat_implies_entails f1575 [c1557, c17] c1575 unsat1575 (by rfl) a
  have h0 : Entails.eval a c1557 := derived1557 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1576 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, false), (⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c1245, some c250, some c652, some c77, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1576 : lratChecker f1576 p1576 = .success := by decide +kernel
theorem unsat1576 : Unsatisfiable (PosFin 57) f1576 := by
  apply lratCheckerSound f1576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1576
  · intro a ha; simp [p1576] at ha; subst a; trivial
  · exact checked1576
theorem derived1576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1576 := by
  apply localUnsat_implies_entails f1576 [c263, c1245, c250, c652, c77] c1576 unsat1576 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c1245 := derived1245 a h
  have h2 : Entails.eval a c250 := h 249 (by decide)
  have h3 : Entails.eval a c652 := derived652 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1577 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1531, some c1576, some c32, some c25, some c260, some c652, some c172, some c1203, some c363, some c259, some c368, some c231, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1577 : lratChecker f1577 p1577 = .success := by decide +kernel
theorem unsat1577 : Unsatisfiable (PosFin 57) f1577 := by
  apply lratCheckerSound f1577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1577
  · intro a ha; simp [p1577] at ha; subst a; trivial
  · exact checked1577
theorem derived1577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1577 := by
  apply localUnsat_implies_entails f1577 [c1531, c1576, c32, c25, c260, c652, c172, c1203, c363, c259, c368, c231] c1577 unsat1577 (by rfl) a
  have h0 : Entails.eval a c1531 := derived1531 a h
  have h1 : Entails.eval a c1576 := derived1576 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c652 := derived652 a h
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c1203 := derived1203 a h
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1578 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1485, some c1542, some c1509, some c106, some c1545, some c105, some c1561, some c1571, some c1574, some c19, some c1575, some c1577, some c8, some c263, some c264, some c1245, some c634, some c24, some c113, some c172, some c1569, some c84, some c1143, some c689, some c166, some c357, some c674, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1578 : lratChecker f1578 p1578 = .success := by decide +kernel
theorem unsat1578 : Unsatisfiable (PosFin 57) f1578 := by
  apply lratCheckerSound f1578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1578
  · intro a ha; simp [p1578] at ha; subst a; trivial
  · exact checked1578
theorem derived1578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1578 := by
  apply localUnsat_implies_entails f1578 [c1485, c1542, c1509, c106, c1545, c105, c1561, c1571, c1574, c19, c1575, c1577, c8, c263, c264, c1245, c634, c24, c113, c172, c1569, c84, c1143, c689, c166, c357, c674] c1578 unsat1578 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1542 := derived1542 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1561 := derived1561 a h
  have h7 : Entails.eval a c1571 := derived1571 a h
  have h8 : Entails.eval a c1574 := derived1574 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1575 := derived1575 a h
  have h11 : Entails.eval a c1577 := derived1577 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c1245 := derived1245 a h
  have h16 : Entails.eval a c634 := derived634 a h
  have h17 : Entails.eval a c24 := h 23 (by decide)
  have h18 : Entails.eval a c113 := h 112 (by decide)
  have h19 : Entails.eval a c172 := h 171 (by decide)
  have h20 : Entails.eval a c1569 := derived1569 a h
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c1143 := derived1143 a h
  have h23 : Entails.eval a c689 := derived689 a h
  have h24 : Entails.eval a c166 := h 165 (by decide)
  have h25 : Entails.eval a c357 := h 356 (by decide)
  have h26 : Entails.eval a c674 := derived674 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1579 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1571, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c8, some c19, some c1575, some c1577, some c1578, some c32, some c25, some c248, some c260, some c172, some c2, some c24, some c193, some c1203, some c188, some c259, some c377, some c683, some c178, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1579 : lratChecker f1579 p1579 = .success := by decide +kernel
theorem unsat1579 : Unsatisfiable (PosFin 57) f1579 := by
  apply lratCheckerSound f1579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1579
  · intro a ha; simp [p1579] at ha; subst a; trivial
  · exact checked1579
theorem derived1579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1579 := by
  apply localUnsat_implies_entails f1579 [c1574, c1571, c1561, c1485, c1509, c106, c1542, c1545, c105, c8, c19, c1575, c1577, c1578, c32, c25, c248, c260, c172, c2, c24, c193, c1203, c188, c259, c377, c683, c178] c1579 unsat1579 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1571 := derived1571 a h
  have h2 : Entails.eval a c1561 := derived1561 a h
  have h3 : Entails.eval a c1485 := derived1485 a h
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c1542 := derived1542 a h
  have h7 : Entails.eval a c1545 := derived1545 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c1575 := derived1575 a h
  have h12 : Entails.eval a c1577 := derived1577 a h
  have h13 : Entails.eval a c1578 := derived1578 a h
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c260 := h 259 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  have h22 : Entails.eval a c1203 := derived1203 a h
  have h23 : Entails.eval a c188 := h 187 (by decide)
  have h24 : Entails.eval a c259 := h 258 (by decide)
  have h25 : Entails.eval a c377 := h 376 (by decide)
  have h26 : Entails.eval a c683 := derived683 a h
  have h27 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1580 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1561, some c184, some c1579, some c1574, some c1571, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c263, some c264, some c634, some c190, some c188, some c1330, some c665, some c51, some c67, some c131, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1580 : lratChecker f1580 p1580 = .success := by decide +kernel
theorem unsat1580 : Unsatisfiable (PosFin 57) f1580 := by
  apply lratCheckerSound f1580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1580
  · intro a ha; simp [p1580] at ha; subst a; trivial
  · exact checked1580
theorem derived1580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1580 := by
  apply localUnsat_implies_entails f1580 [c1561, c184, c1579, c1574, c1571, c1485, c1509, c106, c1542, c1545, c105, c263, c264, c634, c190, c188, c1330, c665, c51, c67, c131] c1580 unsat1580 (by rfl) a
  have h0 : Entails.eval a c1561 := derived1561 a h
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c1579 := derived1579 a h
  have h3 : Entails.eval a c1574 := derived1574 a h
  have h4 : Entails.eval a c1571 := derived1571 a h
  have h5 : Entails.eval a c1485 := derived1485 a h
  have h6 : Entails.eval a c1509 := derived1509 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c1542 := derived1542 a h
  have h9 : Entails.eval a c1545 := derived1545 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c634 := derived634 a h
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c1330 := derived1330 a h
  have h17 : Entails.eval a c665 := derived665 a h
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c67 := h 66 (by decide)
  have h20 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1581 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1579, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c105, some c184, some c1580, some c32, some c120, some c2, some c1496, some c380, some c190, some c188, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1581 : lratChecker f1581 p1581 = .success := by decide +kernel
theorem unsat1581 : Unsatisfiable (PosFin 57) f1581 := by
  apply lratCheckerSound f1581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1581
  · intro a ha; simp [p1581] at ha; subst a; trivial
  · exact checked1581
theorem derived1581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1581 := by
  apply localUnsat_implies_entails f1581 [c1579, c1561, c1485, c1509, c106, c1542, c1545, c105, c184, c1580, c32, c120, c2, c1496, c380, c190, c188] c1581 unsat1581 (by rfl) a
  have h0 : Entails.eval a c1579 := derived1579 a h
  have h1 : Entails.eval a c1561 := derived1561 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1542 := derived1542 a h
  have h6 : Entails.eval a c1545 := derived1545 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c1580 := derived1580 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c1496 := derived1496 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1582 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1581, some c1579, some c1574, some c1571, some c1561, some c1485, some c1509, some c106, some c1542, some c1545, some c263, some c264, some c634, some c1203, some c190, some c24, some c188, some c1034, some c74, some c2, some c166, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1582 : lratChecker f1582 p1582 = .success := by decide +kernel
theorem unsat1582 : Unsatisfiable (PosFin 57) f1582 := by
  apply lratCheckerSound f1582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1582
  · intro a ha; simp [p1582] at ha; subst a; trivial
  · exact checked1582
theorem derived1582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1582 := by
  apply localUnsat_implies_entails f1582 [c1581, c1579, c1574, c1571, c1561, c1485, c1509, c106, c1542, c1545, c263, c264, c634, c1203, c190, c24, c188, c1034, c74, c2, c166] c1582 unsat1582 (by rfl) a
  have h0 : Entails.eval a c1581 := derived1581 a h
  have h1 : Entails.eval a c1579 := derived1579 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c1571 := derived1571 a h
  have h4 : Entails.eval a c1561 := derived1561 a h
  have h5 : Entails.eval a c1485 := derived1485 a h
  have h6 : Entails.eval a c1509 := derived1509 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c1542 := derived1542 a h
  have h9 : Entails.eval a c1545 := derived1545 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c634 := derived634 a h
  have h13 : Entails.eval a c1203 := derived1203 a h
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c1034 := derived1034 a h
  have h18 : Entails.eval a c74 := h 73 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1583 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1542, some c1509, some c106, some c1485, some c1545, some c105, some c1561, some c1571, some c1574, some c1579, some c1581, some c1582, some c32, some c25, some c120, some c260, some c2, some c12, some c248, some c172, some c80, some c24, some c1203, some c259, some c231, some c1255, some c368, some c367, some c363, some c380, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1583 : lratChecker f1583 p1583 = .success := by decide +kernel
theorem unsat1583 : Unsatisfiable (PosFin 57) f1583 := by
  apply lratCheckerSound f1583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1583
  · intro a ha; simp [p1583] at ha; subst a; trivial
  · exact checked1583
theorem derived1583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1583 := by
  apply localUnsat_implies_entails f1583 [c1542, c1509, c106, c1485, c1545, c105, c1561, c1571, c1574, c1579, c1581, c1582, c32, c25, c120, c260, c2, c12, c248, c172, c80, c24, c1203, c259, c231, c1255, c368, c367, c363, c380] c1583 unsat1583 (by rfl) a
  have h0 : Entails.eval a c1542 := derived1542 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1485 := derived1485 a h
  have h4 : Entails.eval a c1545 := derived1545 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1561 := derived1561 a h
  have h7 : Entails.eval a c1571 := derived1571 a h
  have h8 : Entails.eval a c1574 := derived1574 a h
  have h9 : Entails.eval a c1579 := derived1579 a h
  have h10 : Entails.eval a c1581 := derived1581 a h
  have h11 : Entails.eval a c1582 := derived1582 a h
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c248 := h 247 (by decide)
  have h19 : Entails.eval a c172 := h 171 (by decide)
  have h20 : Entails.eval a c80 := h 79 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c1203 := derived1203 a h
  have h23 : Entails.eval a c259 := h 258 (by decide)
  have h24 : Entails.eval a c231 := h 230 (by decide)
  have h25 : Entails.eval a c1255 := derived1255 a h
  have h26 : Entails.eval a c368 := h 367 (by decide)
  have h27 : Entails.eval a c367 := h 366 (by decide)
  have h28 : Entails.eval a c363 := h 362 (by decide)
  have h29 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1583

end CochromaticTwenty.Certificates.B16_2_2
