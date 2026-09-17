import MerLeanExperiment.Certificates.B16_7_2.Steps1000_1099

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1489 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c285, some c272, some c53, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 57) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c1486, c285, c272, c53] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1488, some c57, some c71, some c1489, some c43, some c33, some c296, some c75, some c81, some c357, some c360, some c95, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 57) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1486, c1488, c57, c71, c1489, c43, c33, c296, c75, c81, c357, c360, c95] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1488 := derived1488 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c1489 := derived1489 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨25, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1490, some c37, some c53, some c63, some c288, some c344, some c83, some c87, some c357, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 57) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c1486, c1490, c37, c53, c63, c288, c344, c83, c87, c357] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1490 := derived1490 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1490, some c37, some c1491, some c272, some c333, some c69, some c87, some c344, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 57) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c1486, c1490, c37, c1491, c272, c333, c69, c87, c344] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1490 := derived1490 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c1491 := derived1491 a h
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c102, some c101, some c1490, some c37, some c1492, some c33, some c333, some c53, some c63, some c357, some c344, some c83, some c1194, some c360, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 57) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1486, c102, c101, c1490, c37, c1492, c33, c333, c53, c63, c357, c344, c83, c1194, c360] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c1490 := derived1490 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1492 := derived1492 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c1194 := derived1194 a h
  have h14 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1494 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨40, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c272, some c53, some c288, some c357, some c81, some c87, some c368, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 57) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1486, c272, c53, c288, c357, c81, c87, c368] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c101, some c102, some c1490, some c37, some c1493, some c57, some c71, some c1494, some c33, some c357, some c53, some c75, some c336, some c368, some c1194, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 57) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c1486, c101, c102, c1490, c37, c1493, c57, c71, c1494, c33, c357, c53, c75, c336, c368, c1194] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c1490 := derived1490 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1493 := derived1493 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c1494 := derived1494 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c1194 := derived1194 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c102, some c101, some c1495, some c40, some c51, some c49, some c701, some c319, some c139, some c47, some c11, some c147, some c107, some c21, some c27, some c205, some c317, some c312, some c146, some c386, some c382, some c405, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 57) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c908, c102, c101, c1495, c40, c51, c49, c701, c319, c139, c47, c11, c147, c107, c21, c27, c205, c317, c312, c146, c386, c382, c405] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c1495 := derived1495 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c386 := h 385 (by decide)
  have h21 : Entails.eval a c382 := h 381 (by decide)
  have h22 : Entails.eval a c405 := derived405 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨25, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c33, some c41, some c276, some c61, some c333, some c336, some c95, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 57) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1486, c33, c41, c276, c61, c333, c336, c95] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c276 := h 275 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c336 := h 335 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c41, some c33, some c1497, some c60, some c292, some c76, some c73, some c357, some c360, some c95, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 57) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1486, c41, c33, c1497, c60, c292, c76, c73, c357, c360, c95] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c1497 := derived1497 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c272, some c276, some c61, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 57) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1486, c272, c276, c61] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1498, some c1487, some c44, some c1499, some c60, some c288, some c292, some c73, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 57) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1486, c1498, c1487, c44, c1499, c60, c288, c292, c73] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1498 := derived1498 a h
  have h2 : Entails.eval a c1487 := derived1487 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c1499 := derived1499 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1500, some c64, some c57, some c71, some c276, some c44, some c41, some c1489, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 57) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1486, c1500, c64, c57, c71, c276, c44, c41, c1489] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1500 := derived1500 a h
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c1489 := derived1489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, false), (⟨38, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c278, some c136, some c13, some c9, some c158, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 57) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c319, c278, c136, c13, c9, c158] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨33, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c63, some c280, some c338, some c36, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 57) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1486, c63, c280, c338, c36] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c280 := h 279 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨38, by decide⟩, true), (⟨42, by decide⟩, false), (⟨34, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c269, some c1503, some c384, some c385, some c338, some c362, some c1137, some c216, some c278, some c29, some c62, some c226, some c25, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 57) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1486, c269, c1503, c384, c385, c338, c362, c1137, c216, c278, c29, c62, c226, c25] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c1503 := derived1503 a h
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c1137 := derived1137 a h
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨36, by decide⟩, true), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c155, some c420, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p1505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 57) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c189, c155, c420] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c420 := derived420 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨38, by decide⟩, true), (⟨26, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c479, some c754, some c196, some c106, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 57) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c13, c479, c754, c196, c106] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c479 := derived479 a h
  have h2 : Entails.eval a c754 := derived754 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨42, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c269, some c61, some c314, some c276, some c354, some c34, some c340, some c1503, some c1504, some c1506, some c136, some c1505, some c280, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 57) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1486, c269, c61, c314, c276, c354, c34, c340, c1503, c1504, c1506, c136, c1505, c280] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  have h8 : Entails.eval a c1503 := derived1503 a h
  have h9 : Entails.eval a c1504 := derived1504 a h
  have h10 : Entails.eval a c1506 := derived1506 a h
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c1505 := derived1505 a h
  have h13 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1496, some c908, some c1501, some c314, some c269, some c53, some c285, some c288, some c76, some c1507, some c220, some c32, some c31, some c212, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 57) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1486, c1496, c908, c1501, c314, c269, c53, c285, c288, c76, c1507, c220, c32, c31, c212] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1501 := derived1501 a h
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c1507 := derived1507 a h
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c31 := h 30 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c43, some c280, some c290, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 57) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1486, c43, c280, c290, c56] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c280 := h 279 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c41, some c276, some c54, some c1509, some c33, some c61, some c333, some c88, some c318, some c384, some c385, some c306, some c138, some c873, some c1447, some c278, some c13, some c55, some c1148, some c25, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 57) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c1486, c41, c276, c54, c1509, c33, c61, c333, c88, c318, c384, c385, c306, c138, c873, c1447, c278, c13, c55, c1148, c25] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c873 := derived873 a h
  have h15 : Entails.eval a c1447 := derived1447 a h
  have h16 : Entails.eval a c278 := h 277 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c55 := h 54 (by decide)
  have h19 : Entails.eval a c1148 := derived1148 a h
  have h20 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨36, by decide⟩, true), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c160, some c16, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 57) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c189, c160, c16] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c479, some c754, some c196, some c114, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 57) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c13, c479, c754, c196, c114] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c479 := derived479 a h
  have h2 : Entails.eval a c754 := derived754 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c41, some c318, some c33, some c908, some c1501, some c276, some c54, some c61, some c349, some c350, some c333, some c336, some c88, some c1509, some c1510, some c1512, some c136, some c1511, some c280, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 57) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c1486, c41, c318, c33, c908, c1501, c276, c54, c61, c349, c350, c333, c336, c88, c1509, c1510, c1512, c136, c1511, c280] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1501 := derived1501 a h
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c350 := h 349 (by decide)
  have h11 : Entails.eval a c333 := h 332 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c1509 := derived1509 a h
  have h15 : Entails.eval a c1510 := derived1510 a h
  have h16 : Entails.eval a c1512 := derived1512 a h
  have h17 : Entails.eval a c136 := h 135 (by decide)
  have h18 : Entails.eval a c1511 := derived1511 a h
  have h19 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c41, some c43, some c1509, some c280, some c76, some c56, some c296, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 57) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c1486, c41, c43, c1509, c280, c76, c56, c296] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c1509 := derived1509 a h
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c385, some c312, some c306, some c138, some c701, some c319, some c15, some c13, some c143, some c191, some c148, some c193, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 57) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c384, c385, c312, c306, c138, c701, c319, c15, c13, c143, c191, c148, c193] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c319 := h 318 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c16, some c152, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 57) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c15, c16, c152] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1496, some c908, some c1501, some c1508, some c41, some c318, some c1513, some c1516, some c120, some c32, some c31, some c212, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 57) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1486, c1496, c908, c1501, c1508, c41, c318, c1513, c1516, c120, c32, c31, c212] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1501 := derived1501 a h
  have h4 : Entails.eval a c1508 := derived1508 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c1513 := derived1513 a h
  have h8 : Entails.eval a c1516 := derived1516 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c31, some c212, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 57) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c32, c31, c212] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1496, some c908, some c1501, some c1517, some c37, some c44, some c318, some c1516, some c1518, some c120, some c276, some c1499, some c61, some c33, some c333, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 57) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c1486, c1496, c908, c1501, c1517, c37, c44, c318, c1516, c1518, c120, c276, c1499, c61, c33, c333] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1501 := derived1501 a h
  have h4 : Entails.eval a c1517 := derived1517 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c318 := h 317 (by decide)
  have h8 : Entails.eval a c1516 := derived1516 a h
  have h9 : Entails.eval a c1518 := derived1518 a h
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c276 := h 275 (by decide)
  have h12 : Entails.eval a c1499 := derived1499 a h
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1519, some c57, some c1496, some c64, some c1501, some c314, some c1516, some c1518, some c120, some c276, some c1489, some c44, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 57) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c908, c1519, c57, c1496, c64, c1501, c314, c1516, c1518, c120, c276, c1489, c44] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1519 := derived1519 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c1496 := derived1496 a h
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c1501 := derived1501 a h
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c1516 := derived1516 a h
  have h8 : Entails.eval a c1518 := derived1518 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c1489 := derived1489 a h
  have h12 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1521 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1496, some c908, some c1501, some c1519, some c64, some c1520, some c41, some c318, some c276, some c1516, some c1518, some c120, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1521 : lratChecker f1521 p1521 = .success := by decide +kernel
theorem unsat1521 : Unsatisfiable (PosFin 57) f1521 := by
  apply lratCheckerSound f1521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1521
  · intro a ha; simp [p1521] at ha; subst a; trivial
  · exact checked1521
theorem derived1521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1521 := by
  apply localUnsat_implies_entails f1521 [c1486, c1496, c908, c1501, c1519, c64, c1520, c41, c318, c276, c1516, c1518, c120] c1521 unsat1521 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1501 := derived1501 a h
  have h4 : Entails.eval a c1519 := derived1519 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c1520 := derived1520 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c1516 := derived1516 a h
  have h11 : Entails.eval a c1518 := derived1518 a h
  have h12 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1522 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨40, by decide⟩, false), (⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c40, some c83, some c340, some c360, some c85, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1522 : lratChecker f1522 p1522 = .success := by decide +kernel
theorem unsat1522 : Unsatisfiable (PosFin 57) f1522 := by
  apply lratCheckerSound f1522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1522
  · intro a ha; simp [p1522] at ha; subst a; trivial
  · exact checked1522
theorem derived1522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1522 := by
  apply localUnsat_implies_entails f1522 [c1486, c40, c83, c340, c360, c85] c1522 unsat1522 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1523 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1521, some c1516, some c1518, some c112, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1523 : lratChecker f1523 p1523 = .success := by decide +kernel
theorem unsat1523 : Unsatisfiable (PosFin 57) f1523 := by
  apply lratCheckerSound f1523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1523
  · intro a ha; simp [p1523] at ha; subst a; trivial
  · exact checked1523
theorem derived1523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1523 := by
  apply localUnsat_implies_entails f1523 [c1521, c1516, c1518, c112] c1523 unsat1523 (by rfl) a
  have h0 : Entails.eval a c1521 := derived1521 a h
  have h1 : Entails.eval a c1516 := derived1516 a h
  have h2 : Entails.eval a c1518 := derived1518 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1524 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1496, some c269, some c53, some c285, some c76, some c61, some c1521, some c354, some c1522, some c1523, some c286, some c218, some c31, some c112, some c15, some c16, some c139, some c164, some c701, some c356, some c346, some c88, some c62, some c326, some c1503, some c1504, some c1502, some c361, some c307, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1524 : lratChecker f1524 p1524 = .success := by decide +kernel
theorem unsat1524 : Unsatisfiable (PosFin 57) f1524 := by
  apply lratCheckerSound f1524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1524
  · intro a ha; simp [p1524] at ha; subst a; trivial
  · exact checked1524
theorem derived1524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1524 := by
  apply localUnsat_implies_entails f1524 [c1486, c908, c1496, c269, c53, c285, c76, c61, c1521, c354, c1522, c1523, c286, c218, c31, c112, c15, c16, c139, c164, c701, c356, c346, c88, c62, c326, c1503, c1504, c1502, c361, c307] c1524 unsat1524 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c1521 := derived1521 a h
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c1522 := derived1522 a h
  have h11 : Entails.eval a c1523 := derived1523 a h
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c164 := h 163 (by decide)
  have h20 : Entails.eval a c701 := derived701 a h
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c346 := h 345 (by decide)
  have h23 : Entails.eval a c88 := h 87 (by decide)
  have h24 : Entails.eval a c62 := h 61 (by decide)
  have h25 : Entails.eval a c326 := h 325 (by decide)
  have h26 : Entails.eval a c1503 := derived1503 a h
  have h27 : Entails.eval a c1504 := derived1504 a h
  have h28 : Entails.eval a c1502 := derived1502 a h
  have h29 : Entails.eval a c361 := h 360 (by decide)
  have h30 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1525 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c76, some c40, some c83, some c360, some c364, some c85, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1525 : lratChecker f1525 p1525 = .success := by decide +kernel
theorem unsat1525 : Unsatisfiable (PosFin 57) f1525 := by
  apply lratCheckerSound f1525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1525
  · intro a ha; simp [p1525] at ha; subst a; trivial
  · exact checked1525
theorem derived1525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1525 := by
  apply localUnsat_implies_entails f1525 [c1486, c76, c40, c83, c360, c364, c85] c1525 unsat1525 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1526 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨42, by decide⟩, false), (⟨34, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1523, some c1521, some c1496, some c908, some c275, some c317, some c218, some c789, some c31, some c112, some c220, some c1449, some c209, some c15, some c16, some c172, some c1013, some c257, some c253, some c264, some c148, some c124, some c186, some c199, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1526 : lratChecker f1526 p1526 = .success := by decide +kernel
theorem unsat1526 : Unsatisfiable (PosFin 57) f1526 := by
  apply lratCheckerSound f1526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1526
  · intro a ha; simp [p1526] at ha; subst a; trivial
  · exact checked1526
theorem derived1526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1526 := by
  apply localUnsat_implies_entails f1526 [c1523, c1521, c1496, c908, c275, c317, c218, c789, c31, c112, c220, c1449, c209, c15, c16, c172, c1013, c257, c253, c264, c148, c124, c186, c199] c1526 unsat1526 (by rfl) a
  have h0 : Entails.eval a c1523 := derived1523 a h
  have h1 : Entails.eval a c1521 := derived1521 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c789 := derived789 a h
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c1449 := derived1449 a h
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c1013 := derived1013 a h
  have h17 : Entails.eval a c257 := h 256 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c148 := h 147 (by decide)
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c186 := h 185 (by decide)
  have h23 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1527 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨26, by decide⟩, true), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨42, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c111, some c145, some c32, some c172, some c220, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1527 : lratChecker f1527 p1527 = .success := by decide +kernel
theorem unsat1527 : Unsatisfiable (PosFin 57) f1527 := by
  apply lratCheckerSound f1527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1527
  · intro a ha; simp [p1527] at ha; subst a; trivial
  · exact checked1527
theorem derived1527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1527 := by
  apply localUnsat_implies_entails f1527 [c16, c111, c145, c32, c172, c220] c1527 unsat1527 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1528 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1521, some c1496, some c908, some c269, some c61, some c53, some c285, some c76, some c1524, some c1525, some c1523, some c286, some c1526, some c34, some c1527, some c112, some c140, some c32, some c252, some c205, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1528 : lratChecker f1528 p1528 = .success := by decide +kernel
theorem unsat1528 : Unsatisfiable (PosFin 57) f1528 := by
  apply lratCheckerSound f1528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1528
  · intro a ha; simp [p1528] at ha; subst a; trivial
  · exact checked1528
theorem derived1528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1528 := by
  apply localUnsat_implies_entails f1528 [c1486, c1521, c1496, c908, c269, c61, c53, c285, c76, c1524, c1525, c1523, c286, c1526, c34, c1527, c112, c140, c32, c252, c205] c1528 unsat1528 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1521 := derived1521 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c1524 := derived1524 a h
  have h10 : Entails.eval a c1525 := derived1525 a h
  have h11 : Entails.eval a c1523 := derived1523 a h
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c1526 := derived1526 a h
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c1527 := derived1527 a h
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c32 := h 31 (by decide)
  have h19 : Entails.eval a c252 := h 251 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1529 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c1203, some c16, some c164, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1529 : lratChecker f1529 p1529 = .success := by decide +kernel
theorem unsat1529 : Unsatisfiable (PosFin 57) f1529 := by
  apply lratCheckerSound f1529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1529
  · intro a ha; simp [p1529] at ha; subst a; trivial
  · exact checked1529
theorem derived1529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1529 := by
  apply localUnsat_implies_entails f1529 [c140, c1203, c16, c164] c1529 unsat1529 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c1203 := derived1203 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1530 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨36, by decide⟩, true), (⟨30, by decide⟩, false), (⟨26, by decide⟩, false), (⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c317, some c61, some c53, some c63, some c275, some c286, some c218, some c31, some c29, some c209, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1530 : lratChecker f1530 p1530 = .success := by decide +kernel
theorem unsat1530 : Unsatisfiable (PosFin 57) f1530 := by
  apply lratCheckerSound f1530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1530
  · intro a ha; simp [p1530] at ha; subst a; trivial
  · exact checked1530
theorem derived1530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1530 := by
  apply localUnsat_implies_entails f1530 [c1486, c317, c61, c53, c63, c275, c286, c218, c31, c29, c209] c1530 unsat1530 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c275 := h 274 (by decide)
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1531 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1521, some c1496, some c908, some c1528, some c51, some c37, some c44, some c1523, some c317, some c789, some c344, some c1530, some c349, some c270, some c1529, some c701, some c139, some c16, some c704, some c112, some c232, some c31, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1531 : lratChecker f1531 p1531 = .success := by decide +kernel
theorem unsat1531 : Unsatisfiable (PosFin 57) f1531 := by
  apply lratCheckerSound f1531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1531
  · intro a ha; simp [p1531] at ha; subst a; trivial
  · exact checked1531
theorem derived1531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1531 := by
  apply localUnsat_implies_entails f1531 [c1521, c1496, c908, c1528, c51, c37, c44, c1523, c317, c789, c344, c1530, c349, c270, c1529, c701, c139, c16, c704, c112, c232, c31] c1531 unsat1531 (by rfl) a
  have h0 : Entails.eval a c1521 := derived1521 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1528 := derived1528 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1523 := derived1523 a h
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c789 := derived789 a h
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c1530 := derived1530 a h
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c1529 := derived1529 a h
  have h15 : Entails.eval a c701 := derived701 a h
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c704 := derived704 a h
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c232 := h 231 (by decide)
  have h21 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1532 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c336, some c340, some c85, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1532 : lratChecker f1532 p1532 = .success := by decide +kernel
theorem unsat1532 : Unsatisfiable (PosFin 57) f1532 := by
  apply lratCheckerSound f1532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1532
  · intro a ha; simp [p1532] at ha; subst a; trivial
  · exact checked1532
theorem derived1532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1532 := by
  apply localUnsat_implies_entails f1532 [c1486, c336, c340, c85] c1532 unsat1532 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1533 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1521, some c1496, some c350, some c351, some c1532, some c40, some c1529, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1533 : lratChecker f1533 p1533 = .success := by decide +kernel
theorem unsat1533 : Unsatisfiable (PosFin 57) f1533 := by
  apply lratCheckerSound f1533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1533
  · intro a ha; simp [p1533] at ha; subst a; trivial
  · exact checked1533
theorem derived1533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1533 := by
  apply localUnsat_implies_entails f1533 [c1521, c1496, c350, c351, c1532, c40, c1529] c1533 unsat1533 (by rfl) a
  have h0 : Entails.eval a c1521 := derived1521 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c350 := h 349 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c1532 := derived1532 a h
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c1529 := derived1529 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1534 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨38, by decide⟩, true), (⟨42, by decide⟩, false), (⟨33, by decide⟩, false), (⟨37, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1496, some c64, some c1533, some c71, some c1523, some c57, some c1521, some c140, some c1203, some c1529, some c16, some c1527, some c162, some c118, some c139, some c317, some c31, some c335, some c789, some c148, some c209, some c85, some c176, some c29, some c338, some c56, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1534 : lratChecker f1534 p1534 = .success := by decide +kernel
theorem unsat1534 : Unsatisfiable (PosFin 57) f1534 := by
  apply lratCheckerSound f1534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1534
  · intro a ha; simp [p1534] at ha; subst a; trivial
  · exact checked1534
theorem derived1534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1534 := by
  apply localUnsat_implies_entails f1534 [c1486, c908, c1496, c64, c1533, c71, c1523, c57, c1521, c140, c1203, c1529, c16, c1527, c162, c118, c139, c317, c31, c335, c789, c148, c209, c85, c176, c29, c338, c56] c1534 unsat1534 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c1533 := derived1533 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1523 := derived1523 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c1521 := derived1521 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c1203 := derived1203 a h
  have h11 : Entails.eval a c1529 := derived1529 a h
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c1527 := derived1527 a h
  have h14 : Entails.eval a c162 := h 161 (by decide)
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c335 := h 334 (by decide)
  have h20 : Entails.eval a c789 := derived789 a h
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c209 := h 208 (by decide)
  have h23 : Entails.eval a c85 := h 84 (by decide)
  have h24 : Entails.eval a c176 := h 175 (by decide)
  have h25 : Entails.eval a c29 := h 28 (by decide)
  have h26 : Entails.eval a c338 := h 337 (by decide)
  have h27 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1535 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1496, some c1531, some c64, some c1521, some c53, some c73, some c1533, some c71, some c1523, some c270, some c1534, some c701, some c139, some c16, some c112, some c163, some c31, some c200, some c218, some c159, some c377, some c378, some c352, some c329, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1535 : lratChecker f1535 p1535 = .success := by decide +kernel
theorem unsat1535 : Unsatisfiable (PosFin 57) f1535 := by
  apply lratCheckerSound f1535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1535
  · intro a ha; simp [p1535] at ha; subst a; trivial
  · exact checked1535
theorem derived1535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1535 := by
  apply localUnsat_implies_entails f1535 [c1486, c908, c1496, c1531, c64, c1521, c53, c73, c1533, c71, c1523, c270, c1534, c701, c139, c16, c112, c163, c31, c200, c218, c159, c377, c378, c352, c329] c1535 unsat1535 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c1531 := derived1531 a h
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c1521 := derived1521 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c1533 := derived1533 a h
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c1523 := derived1523 a h
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c1534 := derived1534 a h
  have h13 : Entails.eval a c701 := derived701 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c200 := h 199 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c159 := h 158 (by decide)
  have h22 : Entails.eval a c377 := h 376 (by decide)
  have h23 : Entails.eval a c378 := h 377 (by decide)
  have h24 : Entails.eval a c352 := h 351 (by decide)
  have h25 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1536 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1521, some c1496, some c908, some c1531, some c64, some c57, some c1535, some c285, some c51, some c37, some c44, some c1523, some c357, some c317, some c275, some c286, some c85, some c789, some c218, some c338, some c368, some c31, some c216, some c1448, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1536 : lratChecker f1536 p1536 = .success := by decide +kernel
theorem unsat1536 : Unsatisfiable (PosFin 57) f1536 := by
  apply lratCheckerSound f1536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1536
  · intro a ha; simp [p1536] at ha; subst a; trivial
  · exact checked1536
theorem derived1536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1536 := by
  apply localUnsat_implies_entails f1536 [c1486, c1521, c1496, c908, c1531, c64, c57, c1535, c285, c51, c37, c44, c1523, c357, c317, c275, c286, c85, c789, c218, c338, c368, c31, c216, c1448] c1536 unsat1536 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1521 := derived1521 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c1531 := derived1531 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c1535 := derived1535 a h
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c1523 := derived1523 a h
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  have h15 : Entails.eval a c275 := h 274 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c85 := h 84 (by decide)
  have h18 : Entails.eval a c789 := derived789 a h
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c338 := h 337 (by decide)
  have h21 : Entails.eval a c368 := h 367 (by decide)
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c216 := h 215 (by decide)
  have h24 : Entails.eval a c1448 := derived1448 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1537 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨49, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c40, some c336, some c61, some c53, some c340, some c1525, some c88, some c357, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1537 : lratChecker f1537 p1537 = .success := by decide +kernel
theorem unsat1537 : Unsatisfiable (PosFin 57) f1537 := by
  apply lratCheckerSound f1537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1537
  · intro a ha; simp [p1537] at ha; subst a; trivial
  · exact checked1537
theorem derived1537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1537 := by
  apply localUnsat_implies_entails f1537 [c1486, c40, c336, c61, c53, c340, c1525, c88, c357] c1537 unsat1537 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c1525 := derived1525 a h
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1538 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨49, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c40, some c1537, some c60, some c360, some c53, some c73, some c333, some c364, some c88, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1538 : lratChecker f1538 p1538 = .success := by decide +kernel
theorem unsat1538 : Unsatisfiable (PosFin 57) f1538 := by
  apply lratCheckerSound f1538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1538
  · intro a ha; simp [p1538] at ha; subst a; trivial
  · exact checked1538
theorem derived1538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1538 := by
  apply localUnsat_implies_entails f1538 [c1486, c40, c1537, c60, c360, c53, c73, c333, c364, c88] c1538 unsat1538 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c1537 := derived1537 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c360 := h 359 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1539 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1496, some c1521, some c1536, some c33, some c1538, some c1523, some c41, some c61, some c275, some c317, some c140, some c1203, some c1529, some c16, some c356, some c148, some c62, some c158, some c9, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1539 : lratChecker f1539 p1539 = .success := by decide +kernel
theorem unsat1539 : Unsatisfiable (PosFin 57) f1539 := by
  apply lratCheckerSound f1539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1539
  · intro a ha; simp [p1539] at ha; subst a; trivial
  · exact checked1539
theorem derived1539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1539 := by
  apply localUnsat_implies_entails f1539 [c1486, c908, c1496, c1521, c1536, c33, c1538, c1523, c41, c61, c275, c317, c140, c1203, c1529, c16, c356, c148, c62, c158, c9] c1539 unsat1539 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c1521 := derived1521 a h
  have h4 : Entails.eval a c1536 := derived1536 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c1538 := derived1538 a h
  have h7 : Entails.eval a c1523 := derived1523 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c1203 := derived1203 a h
  have h14 : Entails.eval a c1529 := derived1529 a h
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c158 := h 157 (by decide)
  have h20 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1540 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1496, some c1536, some c41, some c908, some c1521, some c33, some c1538, some c1523, some c317, some c61, some c275, some c1539, some c701, some c139, some c16, some c112, some c149, some c31, some c13, some c118, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1540 : lratChecker f1540 p1540 = .success := by decide +kernel
theorem unsat1540 : Unsatisfiable (PosFin 57) f1540 := by
  apply lratCheckerSound f1540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1540
  · intro a ha; simp [p1540] at ha; subst a; trivial
  · exact checked1540
theorem derived1540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1540 := by
  apply localUnsat_implies_entails f1540 [c1486, c1496, c1536, c41, c908, c1521, c33, c1538, c1523, c317, c61, c275, c1539, c701, c139, c16, c112, c149, c31, c13, c118] c1540 unsat1540 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1496 := derived1496 a h
  have h2 : Entails.eval a c1536 := derived1536 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c908 := derived908 a h
  have h5 : Entails.eval a c1521 := derived1521 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c1538 := derived1538 a h
  have h8 : Entails.eval a c1523 := derived1523 a h
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c275 := h 274 (by decide)
  have h12 : Entails.eval a c1539 := derived1539 a h
  have h13 : Entails.eval a c701 := derived701 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1541 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨8, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1521, some c1496, some c1536, some c41, some c1523, some c317, some c789, some c908, some c88, some c384, some c385, some c140, some c1203, some c16, some c186, some c190, some c148, some c199, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1541 : lratChecker f1541 p1541 = .success := by decide +kernel
theorem unsat1541 : Unsatisfiable (PosFin 57) f1541 := by
  apply lratCheckerSound f1541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1541
  · intro a ha; simp [p1541] at ha; subst a; trivial
  · exact checked1541
theorem derived1541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1541 := by
  apply localUnsat_implies_entails f1541 [c1486, c1521, c1496, c1536, c41, c1523, c317, c789, c908, c88, c384, c385, c140, c1203, c16, c186, c190, c148, c199] c1541 unsat1541 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1521 := derived1521 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c1536 := derived1536 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1523 := derived1523 a h
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c789 := derived789 a h
  have h8 : Entails.eval a c908 := derived908 a h
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c1203 := derived1203 a h
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1542 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1536, some c33, some c1496, some c41, some c1521, some c908, some c1514, some c1538, some c1523, some c317, some c789, some c1540, some c333, some c88, some c385, some c384, some c1541, some c701, some c139, some c16, some c149, some c13, some c190, some c918, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1542 : lratChecker f1542 p1542 = .success := by decide +kernel
theorem unsat1542 : Unsatisfiable (PosFin 57) f1542 := by
  apply lratCheckerSound f1542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1542
  · intro a ha; simp [p1542] at ha; subst a; trivial
  · exact checked1542
theorem derived1542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1542 := by
  apply localUnsat_implies_entails f1542 [c1486, c1536, c33, c1496, c41, c1521, c908, c1514, c1538, c1523, c317, c789, c1540, c333, c88, c385, c384, c1541, c701, c139, c16, c149, c13, c190, c918] c1542 unsat1542 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c1496 := derived1496 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1521 := derived1521 a h
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c1514 := derived1514 a h
  have h8 : Entails.eval a c1538 := derived1538 a h
  have h9 : Entails.eval a c1523 := derived1523 a h
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c789 := derived789 a h
  have h12 : Entails.eval a c1540 := derived1540 a h
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c385 := h 384 (by decide)
  have h16 : Entails.eval a c384 := h 383 (by decide)
  have h17 : Entails.eval a c1541 := derived1541 a h
  have h18 : Entails.eval a c701 := derived701 a h
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c149 := h 148 (by decide)
  have h22 : Entails.eval a c13 := h 12 (by decide)
  have h23 : Entails.eval a c190 := h 189 (by decide)
  have h24 : Entails.eval a c918 := derived918 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1543 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨37, by decide⟩, true), (⟨49, by decide⟩, false), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c1537, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1543 : lratChecker f1543 p1543 = .success := by decide +kernel
theorem unsat1543 : Unsatisfiable (PosFin 57) f1543 := by
  apply lratCheckerSound f1543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1543
  · intro a ha; simp [p1543] at ha; subst a; trivial
  · exact checked1543
theorem derived1543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1543 := by
  apply localUnsat_implies_entails f1543 [c71, c1537] c1543 unsat1543 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c1537 := derived1537 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1544 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨38, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c149, some c31, some c13, some c118, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1544 : lratChecker f1544 p1544 = .success := by decide +kernel
theorem unsat1544 : Unsatisfiable (PosFin 57) f1544 := by
  apply lratCheckerSound f1544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1544
  · intro a ha; simp [p1544] at ha; subst a; trivial
  · exact checked1544
theorem derived1544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1544 := by
  apply localUnsat_implies_entails f1544 [c112, c149, c31, c13, c118] c1544 unsat1544 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1545 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨38, by decide⟩, true), (⟨6, by decide⟩, false), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1544, some c15, some c118, some c31, some c29, some c209, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1545 : lratChecker f1545 p1545 = .success := by decide +kernel
theorem unsat1545 : Unsatisfiable (PosFin 57) f1545 := by
  apply lratCheckerSound f1545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1545
  · intro a ha; simp [p1545] at ha; subst a; trivial
  · exact checked1545
theorem derived1545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1545 := by
  apply localUnsat_implies_entails f1545 [c1544, c15, c118, c31, c29, c209] c1545 unsat1545 (by rfl) a
  have h0 : Entails.eval a c1544 := derived1544 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1546 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1536, some c33, some c1496, some c41, some c1521, some c908, some c64, some c1543, some c1523, some c317, some c275, some c43, some c1545, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1546 : lratChecker f1546 p1546 = .success := by decide +kernel
theorem unsat1546 : Unsatisfiable (PosFin 57) f1546 := by
  apply lratCheckerSound f1546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1546
  · intro a ha; simp [p1546] at ha; subst a; trivial
  · exact checked1546
theorem derived1546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1546 := by
  apply localUnsat_implies_entails f1546 [c1486, c1536, c33, c1496, c41, c1521, c908, c64, c1543, c1523, c317, c275, c43, c1545] c1546 unsat1546 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c1496 := derived1496 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1521 := derived1521 a h
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c1543 := derived1543 a h
  have h9 : Entails.eval a c1523 := derived1523 a h
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c275 := h 274 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c1545 := derived1545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1547 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1496, some c1521, some c1536, some c41, some c33, some c1546, some c1538, some c1542, some c1523, some c37, some c317, some c333, some c43, some c1540, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1547 : lratChecker f1547 p1547 = .success := by decide +kernel
theorem unsat1547 : Unsatisfiable (PosFin 57) f1547 := by
  apply lratCheckerSound f1547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1547
  · intro a ha; simp [p1547] at ha; subst a; trivial
  · exact checked1547
theorem derived1547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1547 := by
  apply localUnsat_implies_entails f1547 [c1486, c908, c1496, c1521, c1536, c41, c33, c1546, c1538, c1542, c1523, c37, c317, c333, c43, c1540] c1547 unsat1547 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c1521 := derived1521 a h
  have h4 : Entails.eval a c1536 := derived1536 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c1546 := derived1546 a h
  have h8 : Entails.eval a c1538 := derived1538 a h
  have h9 : Entails.eval a c1542 := derived1542 a h
  have h10 : Entails.eval a c1523 := derived1523 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  have h15 : Entails.eval a c1540 := derived1540 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1548 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c69, some c63, some c336, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1548 : lratChecker f1548 p1548 = .success := by decide +kernel
theorem unsat1548 : Unsatisfiable (PosFin 57) f1548 := by
  apply lratCheckerSound f1548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1548
  · intro a ha; simp [p1548] at ha; subst a; trivial
  · exact checked1548
theorem derived1548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1548 := by
  apply localUnsat_implies_entails f1548 [c1486, c69, c63, c336] c1548 unsat1548 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1549 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1547, some c908, some c102, some c101, some c1495, some c40, some c51, some c49, some c313, some c33, some c1548, some c280, some c57, some c296, some c81, some c75, some c360, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1549 : lratChecker f1549 p1549 = .success := by decide +kernel
theorem unsat1549 : Unsatisfiable (PosFin 57) f1549 := by
  apply lratCheckerSound f1549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1549
  · intro a ha; simp [p1549] at ha; subst a; trivial
  · exact checked1549
theorem derived1549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1549 := by
  apply localUnsat_implies_entails f1549 [c1486, c1547, c908, c102, c101, c1495, c40, c51, c49, c313, c33, c1548, c280, c57, c296, c81, c75, c360] c1549 unsat1549 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1547 := derived1547 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c1495 := derived1495 a h
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c1548 := derived1548 a h
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1550 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1538, some c1543, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1550 : lratChecker f1550 p1550 = .success := by decide +kernel
theorem unsat1550 : Unsatisfiable (PosFin 57) f1550 := by
  apply lratCheckerSound f1550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1550
  · intro a ha; simp [p1550] at ha; subst a; trivial
  · exact checked1550
theorem derived1550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1550 := by
  apply localUnsat_implies_entails f1550 [c1538, c1543] c1550 unsat1550 (by rfl) a
  have h0 : Entails.eval a c1538 := derived1538 a h
  have h1 : Entails.eval a c1543 := derived1543 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1551 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨31, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1501, some c51, some c313, some c33, some c1550, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1551 : lratChecker f1551 p1551 = .success := by decide +kernel
theorem unsat1551 : Unsatisfiable (PosFin 57) f1551 := by
  apply lratCheckerSound f1551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1551
  · intro a ha; simp [p1551] at ha; subst a; trivial
  · exact checked1551
theorem derived1551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1551 := by
  apply localUnsat_implies_entails f1551 [c1486, c1501, c51, c313, c33, c1550] c1551 unsat1551 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1501 := derived1501 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c1550 := derived1550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1552 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c29, some c25, some c206, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1552 : lratChecker f1552 p1552 = .success := by decide +kernel
theorem unsat1552 : Unsatisfiable (PosFin 57) f1552 := by
  apply lratCheckerSound f1552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1552
  · intro a ha; simp [p1552] at ha; subst a; trivial
  · exact checked1552
theorem derived1552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1552 := by
  apply localUnsat_implies_entails f1552 [c29, c25, c206] c1552 unsat1552 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1553 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1549, some c1547, some c315, some c41, some c318, some c908, some c320, some c1514, some c42, some c1552, some c1148, some c13, some c9, some c146, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1553 : lratChecker f1553 p1553 = .success := by decide +kernel
theorem unsat1553 : Unsatisfiable (PosFin 57) f1553 := by
  apply lratCheckerSound f1553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1553
  · intro a ha; simp [p1553] at ha; subst a; trivial
  · exact checked1553
theorem derived1553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1553 := by
  apply localUnsat_implies_entails f1553 [c1486, c1549, c1547, c315, c41, c318, c908, c320, c1514, c42, c1552, c1148, c13, c9, c146] c1553 unsat1553 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c1547 := derived1547 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c908 := derived908 a h
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c1514 := derived1514 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c1552 := derived1552 a h
  have h11 : Entails.eval a c1148 := derived1148 a h
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1554 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1549, some c1547, some c315, some c41, some c318, some c33, some c908, some c1551, some c1553, some c37, some c333, some c61, some c53, some c276, some c357, some c76, some c292, some c220, some c31, some c110, some c210, some c15, some c245, some c113, some c166, some c218, some c353, some c63, some c161, some c13, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1554 : lratChecker f1554 p1554 = .success := by decide +kernel
theorem unsat1554 : Unsatisfiable (PosFin 57) f1554 := by
  apply lratCheckerSound f1554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1554
  · intro a ha; simp [p1554] at ha; subst a; trivial
  · exact checked1554
theorem derived1554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1554 := by
  apply localUnsat_implies_entails f1554 [c1486, c1549, c1547, c315, c41, c318, c33, c908, c1551, c1553, c37, c333, c61, c53, c276, c357, c76, c292, c220, c31, c110, c210, c15, c245, c113, c166, c218, c353, c63, c161, c13] c1554 unsat1554 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c1547 := derived1547 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c1551 := derived1551 a h
  have h9 : Entails.eval a c1553 := derived1553 a h
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c333 := h 332 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c276 := h 275 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c292 := h 291 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c15 := h 14 (by decide)
  have h23 : Entails.eval a c245 := h 244 (by decide)
  have h24 : Entails.eval a c113 := h 112 (by decide)
  have h25 : Entails.eval a c166 := h 165 (by decide)
  have h26 : Entails.eval a c218 := h 217 (by decide)
  have h27 : Entails.eval a c353 := h 352 (by decide)
  have h28 : Entails.eval a c63 := h 62 (by decide)
  have h29 : Entails.eval a c161 := h 160 (by decide)
  have h30 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1555 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c43, some c274, some c296, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1555 : lratChecker f1555 p1555 = .success := by decide +kernel
theorem unsat1555 : Unsatisfiable (PosFin 57) f1555 := by
  apply lratCheckerSound f1555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1555
  · intro a ha; simp [p1555] at ha; subst a; trivial
  · exact checked1555
theorem derived1555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1555 := by
  apply localUnsat_implies_entails f1555 [c1486, c43, c274, c296, c56] c1555 unsat1555 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1556 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c9, some c146, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1556 : lratChecker f1556 p1556 = .success := by decide +kernel
theorem unsat1556 : Unsatisfiable (PosFin 57) f1556 := by
  apply lratCheckerSound f1556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1556
  · intro a ha; simp [p1556] at ha; subst a; trivial
  · exact checked1556
theorem derived1556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1556 := by
  apply localUnsat_implies_entails f1556 [c13, c9, c146] c1556 unsat1556 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1557 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨30, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c320, some c42, some c1555, some c1552, some c1556, some c108, some c116, some c274, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1557 : lratChecker f1557 p1557 = .success := by decide +kernel
theorem unsat1557 : Unsatisfiable (PosFin 57) f1557 := by
  apply lratCheckerSound f1557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1557
  · intro a ha; simp [p1557] at ha; subst a; trivial
  · exact checked1557
theorem derived1557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1557 := by
  apply localUnsat_implies_entails f1557 [c1486, c320, c42, c1555, c1552, c1556, c108, c116, c274] c1557 unsat1557 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c1555 := derived1555 a h
  have h4 : Entails.eval a c1552 := derived1552 a h
  have h5 : Entails.eval a c1556 := derived1556 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1558 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c43, some c75, some c290, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1558 : lratChecker f1558 p1558 = .success := by decide +kernel
theorem unsat1558 : Unsatisfiable (PosFin 57) f1558 := by
  apply lratCheckerSound f1558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1558
  · intro a ha; simp [p1558] at ha; subst a; trivial
  · exact checked1558
theorem derived1558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1558 := by
  apply localUnsat_implies_entails f1558 [c1486, c43, c75, c290] c1558 unsat1558 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1559 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1547, some c1549, some c1551, some c315, some c41, some c33, some c318, some c1554, some c64, some c57, some c276, some c1557, some c37, some c357, some c73, some c292, some c220, some c31, some c110, some c210, some c15, some c1558, some c13, some c906, some c161, some c274, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1559 : lratChecker f1559 p1559 = .success := by decide +kernel
theorem unsat1559 : Unsatisfiable (PosFin 57) f1559 := by
  apply lratCheckerSound f1559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1559
  · intro a ha; simp [p1559] at ha; subst a; trivial
  · exact checked1559
theorem derived1559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1559 := by
  apply localUnsat_implies_entails f1559 [c1486, c908, c1547, c1549, c1551, c315, c41, c33, c318, c1554, c64, c57, c276, c1557, c37, c357, c73, c292, c220, c31, c110, c210, c15, c1558, c13, c906, c161, c274] c1559 unsat1559 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1547 := derived1547 a h
  have h3 : Entails.eval a c1549 := derived1549 a h
  have h4 : Entails.eval a c1551 := derived1551 a h
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c1554 := derived1554 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c1557 := derived1557 a h
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c292 := h 291 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c15 := h 14 (by decide)
  have h23 : Entails.eval a c1558 := derived1558 a h
  have h24 : Entails.eval a c13 := h 12 (by decide)
  have h25 : Entails.eval a c906 := derived906 a h
  have h26 : Entails.eval a c161 := h 160 (by decide)
  have h27 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1560 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨42, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c316, some c317, some c274, some c290, some c42, some c216, some c1552, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1560 : lratChecker f1560 p1560 = .success := by decide +kernel
theorem unsat1560 : Unsatisfiable (PosFin 57) f1560 := by
  apply lratCheckerSound f1560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1560
  · intro a ha; simp [p1560] at ha; subst a; trivial
  · exact checked1560
theorem derived1560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1560 := by
  apply localUnsat_implies_entails f1560 [c1486, c316, c317, c274, c290, c42, c216, c1552] c1560 unsat1560 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c1552 := derived1552 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1561 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1549, some c908, some c44, some c37, some c57, some c64, some c1559, some c1547, some c1551, some c33, some c357, some c53, some c73, some c1558, some c1560, some c1545, some c354, some c275, some c334, some c353, some c138, some c15, some c13, some c161, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1561 : lratChecker f1561 p1561 = .success := by decide +kernel
theorem unsat1561 : Unsatisfiable (PosFin 57) f1561 := by
  apply lratCheckerSound f1561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1561
  · intro a ha; simp [p1561] at ha; subst a; trivial
  · exact checked1561
theorem derived1561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1561 := by
  apply localUnsat_implies_entails f1561 [c1486, c1549, c908, c44, c37, c57, c64, c1559, c1547, c1551, c33, c357, c53, c73, c1558, c1560, c1545, c354, c275, c334, c353, c138, c15, c13, c161] c1561 unsat1561 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c1559 := derived1559 a h
  have h8 : Entails.eval a c1547 := derived1547 a h
  have h9 : Entails.eval a c1551 := derived1551 a h
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c1558 := derived1558 a h
  have h15 : Entails.eval a c1560 := derived1560 a h
  have h16 : Entails.eval a c1545 := derived1545 a h
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c275 := h 274 (by decide)
  have h19 : Entails.eval a c334 := h 333 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c138 := h 137 (by decide)
  have h22 : Entails.eval a c15 := h 14 (by decide)
  have h23 : Entails.eval a c13 := h 12 (by decide)
  have h24 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1562 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨45, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c73, some c75, some c368, some c290, some c36, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1562 : lratChecker f1562 p1562 = .success := by decide +kernel
theorem unsat1562 : Unsatisfiable (PosFin 57) f1562 := by
  apply lratCheckerSound f1562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1562
  · intro a ha; simp [p1562] at ha; subst a; trivial
  · exact checked1562
theorem derived1562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1562 := by
  apply localUnsat_implies_entails f1562 [c1486, c73, c75, c368, c290, c36] c1562 unsat1562 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1563 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1562, some c357, some c85, some c87, some c338, some c368, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1563 : lratChecker f1563 p1563 = .success := by decide +kernel
theorem unsat1563 : Unsatisfiable (PosFin 57) f1563 := by
  apply lratCheckerSound f1563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1563
  · intro a ha; simp [p1563] at ha; subst a; trivial
  · exact checked1563
theorem derived1563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1563 := by
  apply localUnsat_implies_entails f1563 [c1486, c1562, c357, c85, c87, c338, c368, c56] c1563 unsat1563 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1562 := derived1562 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1564 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨39, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c316, some c317, some c274, some c290, some c216, some c328, some c1552, some c380, some c74, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1564 : lratChecker f1564 p1564 = .success := by decide +kernel
theorem unsat1564 : Unsatisfiable (PosFin 57) f1564 := by
  apply lratCheckerSound f1564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1564
  · intro a ha; simp [p1564] at ha; subst a; trivial
  · exact checked1564
theorem derived1564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1564 := by
  apply localUnsat_implies_entails f1564 [c1486, c316, c317, c274, c290, c216, c328, c1552, c380, c74] c1564 unsat1564 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c1552 := derived1552 a h
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1565 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1549, some c908, some c64, some c57, some c37, some c44, some c1563, some c1561, some c1559, some c1547, some c1551, some c357, some c53, some c73, some c271, some c1564, some c1545, some c354, some c275, some c334, some c353, some c138, some c15, some c13, some c161, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1565 : lratChecker f1565 p1565 = .success := by decide +kernel
theorem unsat1565 : Unsatisfiable (PosFin 57) f1565 := by
  apply lratCheckerSound f1565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1565
  · intro a ha; simp [p1565] at ha; subst a; trivial
  · exact checked1565
theorem derived1565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1565 := by
  apply localUnsat_implies_entails f1565 [c1486, c1549, c908, c64, c57, c37, c44, c1563, c1561, c1559, c1547, c1551, c357, c53, c73, c271, c1564, c1545, c354, c275, c334, c353, c138, c15, c13, c161] c1565 unsat1565 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1563 := derived1563 a h
  have h8 : Entails.eval a c1561 := derived1561 a h
  have h9 : Entails.eval a c1559 := derived1559 a h
  have h10 : Entails.eval a c1547 := derived1547 a h
  have h11 : Entails.eval a c1551 := derived1551 a h
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c1564 := derived1564 a h
  have h17 : Entails.eval a c1545 := derived1545 a h
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c275 := h 274 (by decide)
  have h20 : Entails.eval a c334 := h 333 (by decide)
  have h21 : Entails.eval a c353 := h 352 (by decide)
  have h22 : Entails.eval a c138 := h 137 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c13 := h 12 (by decide)
  have h25 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1566 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c29, some c210, some c206, some c267, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1566 : lratChecker f1566 p1566 = .success := by decide +kernel
theorem unsat1566 : Unsatisfiable (PosFin 57) f1566 := by
  apply lratCheckerSound f1566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1566
  · intro a ha; simp [p1566] at ha; subst a; trivial
  · exact checked1566
theorem derived1566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1566 := by
  apply localUnsat_implies_entails f1566 [c29, c210, c206, c267] c1566 unsat1566 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1567 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨45, by decide⟩, false), (⟨34, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c317, some c274, some c1566, some c116, some c216, some c13, some c176, some c150, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1567 : lratChecker f1567 p1567 = .success := by decide +kernel
theorem unsat1567 : Unsatisfiable (PosFin 57) f1567 := by
  apply lratCheckerSound f1567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1567
  · intro a ha; simp [p1567] at ha; subst a; trivial
  · exact checked1567
theorem derived1567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1567 := by
  apply localUnsat_implies_entails f1567 [c316, c317, c274, c1566, c116, c216, c13, c176, c150] c1567 unsat1567 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c1566 := derived1566 a h
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1568 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c57, some c1549, some c64, some c1559, some c1547, some c1551, some c37, some c44, some c1563, some c1565, some c85, some c1567, some c1545, some c354, some c275, some c353, some c339, some c138, some c15, some c13, some c161, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1568 : lratChecker f1568 p1568 = .success := by decide +kernel
theorem unsat1568 : Unsatisfiable (PosFin 57) f1568 := by
  apply lratCheckerSound f1568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1568
  · intro a ha; simp [p1568] at ha; subst a; trivial
  · exact checked1568
theorem derived1568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1568 := by
  apply localUnsat_implies_entails f1568 [c1486, c908, c57, c1549, c64, c1559, c1547, c1551, c37, c44, c1563, c1565, c85, c1567, c1545, c354, c275, c353, c339, c138, c15, c13, c161] c1568 unsat1568 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c1549 := derived1549 a h
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c1559 := derived1559 a h
  have h6 : Entails.eval a c1547 := derived1547 a h
  have h7 : Entails.eval a c1551 := derived1551 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c1563 := derived1563 a h
  have h11 : Entails.eval a c1565 := derived1565 a h
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c1567 := derived1567 a h
  have h14 : Entails.eval a c1545 := derived1545 a h
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c275 := h 274 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c138 := h 137 (by decide)
  have h20 : Entails.eval a c15 := h 14 (by decide)
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1569 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1559, some c908, some c1547, some c1549, some c1551, some c64, some c57, some c1568, some c313, some c41, some c1555, some c1557, some c317, some c275, some c1545, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1569 : lratChecker f1569 p1569 = .success := by decide +kernel
theorem unsat1569 : Unsatisfiable (PosFin 57) f1569 := by
  apply lratCheckerSound f1569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1569
  · intro a ha; simp [p1569] at ha; subst a; trivial
  · exact checked1569
theorem derived1569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1569 := by
  apply localUnsat_implies_entails f1569 [c1486, c1559, c908, c1547, c1549, c1551, c64, c57, c1568, c313, c41, c1555, c1557, c317, c275, c1545] c1569 unsat1569 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1559 := derived1559 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c1547 := derived1547 a h
  have h4 : Entails.eval a c1549 := derived1549 a h
  have h5 : Entails.eval a c1551 := derived1551 a h
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c1568 := derived1568 a h
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c1555 := derived1555 a h
  have h12 : Entails.eval a c1557 := derived1557 a h
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c275 := h 274 (by decide)
  have h15 : Entails.eval a c1545 := derived1545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1570 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1562, some c357, some c87, some c344, some c368, some c56, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1570 : lratChecker f1570 p1570 = .success := by decide +kernel
theorem unsat1570 : Unsatisfiable (PosFin 57) f1570 := by
  apply lratCheckerSound f1570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1570
  · intro a ha; simp [p1570] at ha; subst a; trivial
  · exact checked1570
theorem derived1570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1570 := by
  apply localUnsat_implies_entails f1570 [c1486, c1562, c357, c87, c344, c368, c56] c1570 unsat1570 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1562 := derived1562 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1571 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c290, some c56, some c274, some c344, some c61, some c87, some c333, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1571 : lratChecker f1571 p1571 = .success := by decide +kernel
theorem unsat1571 : Unsatisfiable (PosFin 57) f1571 := by
  apply lratCheckerSound f1571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1571
  · intro a ha; simp [p1571] at ha; subst a; trivial
  · exact checked1571
theorem derived1571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1571 := by
  apply localUnsat_implies_entails f1571 [c1486, c290, c56, c274, c344, c61, c87, c333] c1571 unsat1571 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1572 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1571, some c36, some c344, some c63, some c56, some c333, some c362, some c85, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1572 : lratChecker f1572 p1572 = .success := by decide +kernel
theorem unsat1572 : Unsatisfiable (PosFin 57) f1572 := by
  apply lratCheckerSound f1572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1572
  · intro a ha; simp [p1572] at ha; subst a; trivial
  · exact checked1572
theorem derived1572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1572 := by
  apply localUnsat_implies_entails f1572 [c1486, c1571, c36, c344, c63, c56, c333, c362, c85] c1572 unsat1572 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1571 := derived1571 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1573 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c37, some c1570, some c76, some c1572, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1573 : lratChecker f1573 p1573 = .success := by decide +kernel
theorem unsat1573 : Unsatisfiable (PosFin 57) f1573 := by
  apply lratCheckerSound f1573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1573
  · intro a ha; simp [p1573] at ha; subst a; trivial
  · exact checked1573
theorem derived1573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1573 := by
  apply localUnsat_implies_entails f1573 [c44, c37, c1570, c76, c1572] c1573 unsat1573 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c1570 := derived1570 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c1572 := derived1572 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1574 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c188, some c16, some c193, some c151, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1574 : lratChecker f1574 p1574 = .success := by decide +kernel
theorem unsat1574 : Unsatisfiable (PosFin 57) f1574 := by
  apply lratCheckerSound f1574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1574
  · intro a ha; simp [p1574] at ha; subst a; trivial
  · exact checked1574
theorem derived1574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1574 := by
  apply localUnsat_implies_entails f1574 [c183, c188, c16, c193, c151] c1574 unsat1574 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c188 := h 187 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1575 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1549, some c1569, some c1573, some c44, some c37, some c1559, some c1547, some c1551, some c316, some c317, some c1567, some c1060, some c1566, some c54, some c61, some c290, some c333, some c216, some c344, some c1574, some c13, some c150, some c146, some c199, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1575 : lratChecker f1575 p1575 = .success := by decide +kernel
theorem unsat1575 : Unsatisfiable (PosFin 57) f1575 := by
  apply lratCheckerSound f1575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1575
  · intro a ha; simp [p1575] at ha; subst a; trivial
  · exact checked1575
theorem derived1575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1575 := by
  apply localUnsat_implies_entails f1575 [c1486, c908, c1549, c1569, c1573, c44, c37, c1559, c1547, c1551, c316, c317, c1567, c1060, c1566, c54, c61, c290, c333, c216, c344, c1574, c13, c150, c146, c199] c1575 unsat1575 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1549 := derived1549 a h
  have h3 : Entails.eval a c1569 := derived1569 a h
  have h4 : Entails.eval a c1573 := derived1573 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1559 := derived1559 a h
  have h8 : Entails.eval a c1547 := derived1547 a h
  have h9 : Entails.eval a c1551 := derived1551 a h
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c1567 := derived1567 a h
  have h13 : Entails.eval a c1060 := derived1060 a h
  have h14 : Entails.eval a c1566 := derived1566 a h
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c290 := h 289 (by decide)
  have h18 : Entails.eval a c333 := h 332 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c344 := h 343 (by decide)
  have h21 : Entails.eval a c1574 := derived1574 a h
  have h22 : Entails.eval a c13 := h 12 (by decide)
  have h23 : Entails.eval a c150 := h 149 (by decide)
  have h24 : Entails.eval a c146 := h 145 (by decide)
  have h25 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1576 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c333, some c357, some c53, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1576 : lratChecker f1576 p1576 = .success := by decide +kernel
theorem unsat1576 : Unsatisfiable (PosFin 57) f1576 := by
  apply lratCheckerSound f1576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1576
  · intro a ha; simp [p1576] at ha; subst a; trivial
  · exact checked1576
theorem derived1576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1576 := by
  apply localUnsat_implies_entails f1576 [c1486, c333, c357, c53] c1576 unsat1576 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1577 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c275, some c353, some c339, some c138, some c15, some c13, some c161, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1577 : lratChecker f1577 p1577 = .success := by decide +kernel
theorem unsat1577 : Unsatisfiable (PosFin 57) f1577 := by
  apply lratCheckerSound f1577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1577
  · intro a ha; simp [p1577] at ha; subst a; trivial
  · exact checked1577
theorem derived1577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1577 := by
  apply localUnsat_implies_entails f1577 [c354, c275, c353, c339, c138, c15, c13, c161] c1577 unsat1577 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1578 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨30, by decide⟩, true), (⟨50, by decide⟩, false), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c136, some c386, some c13, some c138, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1578 : lratChecker f1578 p1578 = .success := by decide +kernel
theorem unsat1578 : Unsatisfiable (PosFin 57) f1578 := by
  apply lratCheckerSound f1578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1578
  · intro a ha; simp [p1578] at ha; subst a; trivial
  · exact checked1578
theorem derived1578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1578 := by
  apply localUnsat_implies_entails f1578 [c309, c136, c386, c13, c138] c1578 unsat1578 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1579 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨30, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c962, some c256, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1579 : lratChecker f1579 p1579 = .success := by decide +kernel
theorem unsat1579 : Unsatisfiable (PosFin 57) f1579 := by
  apply lratCheckerSound f1579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1579
  · intro a ha; simp [p1579] at ha; subst a; trivial
  · exact checked1579
theorem derived1579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1579 := by
  apply localUnsat_implies_entails f1579 [c962, c256] c1579 unsat1579 (by rfl) a
  have h0 : Entails.eval a c962 := derived962 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1580 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1549, some c1569, some c1573, some c44, some c37, some c1559, some c1547, some c1551, some c1575, some c1545, some c1576, some c85, some c33, some c1577, some c61, some c270, some c1578, some c368, some c1579, some c344, some c216, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1580 : lratChecker f1580 p1580 = .success := by decide +kernel
theorem unsat1580 : Unsatisfiable (PosFin 57) f1580 := by
  apply lratCheckerSound f1580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1580
  · intro a ha; simp [p1580] at ha; subst a; trivial
  · exact checked1580
theorem derived1580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1580 := by
  apply localUnsat_implies_entails f1580 [c1486, c908, c1549, c1569, c1573, c44, c37, c1559, c1547, c1551, c1575, c1545, c1576, c85, c33, c1577, c61, c270, c1578, c368, c1579, c344, c216] c1580 unsat1580 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1549 := derived1549 a h
  have h3 : Entails.eval a c1569 := derived1569 a h
  have h4 : Entails.eval a c1573 := derived1573 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1559 := derived1559 a h
  have h8 : Entails.eval a c1547 := derived1547 a h
  have h9 : Entails.eval a c1551 := derived1551 a h
  have h10 : Entails.eval a c1575 := derived1575 a h
  have h11 : Entails.eval a c1545 := derived1545 a h
  have h12 : Entails.eval a c1576 := derived1576 a h
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c1577 := derived1577 a h
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c1578 := derived1578 a h
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c1579 := derived1579 a h
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1581 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨34, by decide⟩, false), (⟨42, by decide⟩, false), (⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c317, some c290, some c274, some c1566, some c216, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1581 : lratChecker f1581 p1581 = .success := by decide +kernel
theorem unsat1581 : Unsatisfiable (PosFin 57) f1581 := by
  apply lratCheckerSound f1581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1581
  · intro a ha; simp [p1581] at ha; subst a; trivial
  · exact checked1581
theorem derived1581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1581 := by
  apply localUnsat_implies_entails f1581 [c316, c317, c290, c274, c1566, c216] c1581 unsat1581 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c1566 := derived1566 a h
  have h5 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1582 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c29, some c1579, some c110, some c136, some c13, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1582 : lratChecker f1582 p1582 = .success := by decide +kernel
theorem unsat1582 : Unsatisfiable (PosFin 57) f1582 := by
  apply lratCheckerSound f1582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1582
  · intro a ha; simp [p1582] at ha; subst a; trivial
  · exact checked1582
theorem derived1582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1582 := by
  apply localUnsat_implies_entails f1582 [c29, c1579, c110, c136, c13] c1582 unsat1582 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c1579 := derived1579 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1583 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c1549, some c1580, some c76, some c1569, some c1573, some c44, some c37, some c1559, some c1547, some c1551, some c1581, some c1545, some c275, some c1582, some c108, some c209, some c13, some c31, some c110, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1583 : lratChecker f1583 p1583 = .success := by decide +kernel
theorem unsat1583 : Unsatisfiable (PosFin 57) f1583 := by
  apply lratCheckerSound f1583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1583
  · intro a ha; simp [p1583] at ha; subst a; trivial
  · exact checked1583
theorem derived1583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1583 := by
  apply localUnsat_implies_entails f1583 [c908, c1549, c1580, c76, c1569, c1573, c44, c37, c1559, c1547, c1551, c1581, c1545, c275, c1582, c108, c209, c13, c31, c110] c1583 unsat1583 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c1580 := derived1580 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c1569 := derived1569 a h
  have h5 : Entails.eval a c1573 := derived1573 a h
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c1559 := derived1559 a h
  have h9 : Entails.eval a c1547 := derived1547 a h
  have h10 : Entails.eval a c1551 := derived1551 a h
  have h11 : Entails.eval a c1581 := derived1581 a h
  have h12 : Entails.eval a c1545 := derived1545 a h
  have h13 : Entails.eval a c275 := h 274 (by decide)
  have h14 : Entails.eval a c1582 := derived1582 a h
  have h15 : Entails.eval a c108 := h 107 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c31 := h 30 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1584 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1569, some c908, some c37, some c1549, some c1583, some c61, some c333, some c1580, some c76, some c1573, some c44, some c1559, some c1547, some c1551, some c316, some c317, some c290, some c1060, some c1566, some c216, some c344, some c1574, some c13, some c150, some c146, some c199, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1584 : lratChecker f1584 p1584 = .success := by decide +kernel
theorem unsat1584 : Unsatisfiable (PosFin 57) f1584 := by
  apply lratCheckerSound f1584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1584
  · intro a ha; simp [p1584] at ha; subst a; trivial
  · exact checked1584
theorem derived1584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1584 := by
  apply localUnsat_implies_entails f1584 [c1486, c1569, c908, c37, c1549, c1583, c61, c333, c1580, c76, c1573, c44, c1559, c1547, c1551, c316, c317, c290, c1060, c1566, c216, c344, c1574, c13, c150, c146, c199] c1584 unsat1584 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1549 := derived1549 a h
  have h5 : Entails.eval a c1583 := derived1583 a h
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c1580 := derived1580 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c1573 := derived1573 a h
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c1559 := derived1559 a h
  have h13 : Entails.eval a c1547 := derived1547 a h
  have h14 : Entails.eval a c1551 := derived1551 a h
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c290 := h 289 (by decide)
  have h18 : Entails.eval a c1060 := derived1060 a h
  have h19 : Entails.eval a c1566 := derived1566 a h
  have h20 : Entails.eval a c216 := h 215 (by decide)
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c1574 := derived1574 a h
  have h23 : Entails.eval a c13 := h 12 (by decide)
  have h24 : Entails.eval a c150 := h 149 (by decide)
  have h25 : Entails.eval a c146 := h 145 (by decide)
  have h26 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1585 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1569, some c1559, some c908, some c1547, some c1549, some c1551, some c37, some c1573, some c1580, some c76, some c1583, some c61, some c333, some c85, some c33, some c1584, some c1545, some c270, some c1582, some c1578, some c344, some c362, some c216, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1585 : lratChecker f1585 p1585 = .success := by decide +kernel
theorem unsat1585 : Unsatisfiable (PosFin 57) f1585 := by
  apply lratCheckerSound f1585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1585
  · intro a ha; simp [p1585] at ha; subst a; trivial
  · exact checked1585
theorem derived1585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1585 := by
  apply localUnsat_implies_entails f1585 [c1486, c1569, c1559, c908, c1547, c1549, c1551, c37, c1573, c1580, c76, c1583, c61, c333, c85, c33, c1584, c1545, c270, c1582, c1578, c344, c362, c216] c1585 unsat1585 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1559 := derived1559 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c1547 := derived1547 a h
  have h5 : Entails.eval a c1549 := derived1549 a h
  have h6 : Entails.eval a c1551 := derived1551 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c1573 := derived1573 a h
  have h9 : Entails.eval a c1580 := derived1580 a h
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c1583 := derived1583 a h
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c1584 := derived1584 a h
  have h17 : Entails.eval a c1545 := derived1545 a h
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c1582 := derived1582 a h
  have h20 : Entails.eval a c1578 := derived1578 a h
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c362 := h 361 (by decide)
  have h23 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1586 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c908, some c32, some c27, some c1449, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1586 : lratChecker f1586 p1586 = .success := by decide +kernel
theorem unsat1586 : Unsatisfiable (PosFin 57) f1586 := by
  apply lratCheckerSound f1586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1586
  · intro a ha; simp [p1586] at ha; subst a; trivial
  · exact checked1586
theorem derived1586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1586 := by
  apply localUnsat_implies_entails f1586 [c908, c32, c27, c1449] c1586 unsat1586 (by rfl) a
  have h0 : Entails.eval a c908 := derived908 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c1449 := derived1449 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1587 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c908, some c1547, some c1549, some c1551, some c1559, some c1569, some c1585, some c320, some c313, some c282, some c42, some c41, some c1586, some c119, some c16, some c11, some c147, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1587 : lratChecker f1587 p1587 = .success := by decide +kernel
theorem unsat1587 : Unsatisfiable (PosFin 57) f1587 := by
  apply lratCheckerSound f1587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1587
  · intro a ha; simp [p1587] at ha; subst a; trivial
  · exact checked1587
theorem derived1587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1587 := by
  apply localUnsat_implies_entails f1587 [c1486, c908, c1547, c1549, c1551, c1559, c1569, c1585, c320, c313, c282, c42, c41, c1586, c119, c16, c11, c147] c1587 unsat1587 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c1547 := derived1547 a h
  have h3 : Entails.eval a c1549 := derived1549 a h
  have h4 : Entails.eval a c1551 := derived1551 a h
  have h5 : Entails.eval a c1559 := derived1559 a h
  have h6 : Entails.eval a c1569 := derived1569 a h
  have h7 : Entails.eval a c1585 := derived1585 a h
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c1586 := derived1586 a h
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1588 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c37, some c64, some c44, some c1563, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1588 : lratChecker f1588 p1588 = .success := by decide +kernel
theorem unsat1588 : Unsatisfiable (PosFin 57) f1588 := by
  apply lratCheckerSound f1588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1588
  · intro a ha; simp [p1588] at ha; subst a; trivial
  · exact checked1588
theorem derived1588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1588 := by
  apply localUnsat_implies_entails f1588 [c57, c37, c64, c44, c1563] c1588 unsat1588 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c1563 := derived1563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1588

end CochromaticTwenty.Certificates.B16_7_2
