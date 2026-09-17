import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0400_0499

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1417 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1417 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1412, some c1416, some c1367, some c46, some c50, some c157, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1417 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1417 : lratChecker f1417 p1417 = .success := by decide +kernel
theorem unsat1417 : Unsatisfiable (PosFin 31) f1417 := by
  apply lratCheckerSound f1417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1417
  · intro a ha; simp [p1417] at ha; subst a; trivial
  · exact checked1417
theorem derived1417 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1417 := by
  apply localUnsat_implies_entails f1417 [c1412, c1416, c1367, c46, c50, c157] c1417 unsat1417 (by rfl) a
  have h0 : Entails.eval a c1412 := derived1412 a h
  have h1 : Entails.eval a c1416 := derived1416 a h
  have h2 : Entails.eval a c1367 := derived1367 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1418 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1418 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1408, some c1412, some c1417, some c1411, some c1367, some c46, some c1399, some c751, some c35, some c333, some c337, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1418 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1418 : lratChecker f1418 p1418 = .success := by decide +kernel
theorem unsat1418 : Unsatisfiable (PosFin 31) f1418 := by
  apply lratCheckerSound f1418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1418
  · intro a ha; simp [p1418] at ha; subst a; trivial
  · exact checked1418
theorem derived1418 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1418 := by
  apply localUnsat_implies_entails f1418 [c1366, c1408, c1412, c1417, c1411, c1367, c46, c1399, c751, c35, c333, c337] c1418 unsat1418 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1408 := derived1408 a h
  have h2 : Entails.eval a c1412 := derived1412 a h
  have h3 : Entails.eval a c1417 := derived1417 a h
  have h4 : Entails.eval a c1411 := derived1411 a h
  have h5 : Entails.eval a c1367 := derived1367 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c1399 := derived1399 a h
  have h8 : Entails.eval a c751 := h 750 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c333 := h 332 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1419 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1419 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1418, some c1393, some c1366, some c1367, some c50, some c138, some c85, some c192, some c632, some c1330, some c708, some c1215, some c1360, some c383, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1419 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1419 : lratChecker f1419 p1419 = .success := by decide +kernel
theorem unsat1419 : Unsatisfiable (PosFin 31) f1419 := by
  apply lratCheckerSound f1419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1419
  · intro a ha; simp [p1419] at ha; subst a; trivial
  · exact checked1419
theorem derived1419 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1419 := by
  apply localUnsat_implies_entails f1419 [c1418, c1393, c1366, c1367, c50, c138, c85, c192, c632, c1330, c708, c1215, c1360, c383] c1419 unsat1419 (by rfl) a
  have h0 : Entails.eval a c1418 := derived1418 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1367 := derived1367 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c632 := h 631 (by decide)
  have h9 : Entails.eval a c1330 := derived1330 a h
  have h10 : Entails.eval a c708 := h 707 (by decide)
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1360 := derived1360 a h
  have h13 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1420 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1420 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c138, some c85, some c365, some c129, some c252, some c685, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1420 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1420 : lratChecker f1420 p1420 = .success := by decide +kernel
theorem unsat1420 : Unsatisfiable (PosFin 31) f1420 := by
  apply lratCheckerSound f1420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1420
  · intro a ha; simp [p1420] at ha; subst a; trivial
  · exact checked1420
theorem derived1420 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1420 := by
  apply localUnsat_implies_entails f1420 [c138, c85, c365, c129, c252, c685] c1420 unsat1420 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c252 := h 251 (by decide)
  have h5 : Entails.eval a c685 := h 684 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1421 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨28, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1421 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1286, some c502, some c191, some c137, some c84, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1421 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1421 : lratChecker f1421 p1421 = .success := by decide +kernel
theorem unsat1421 : Unsatisfiable (PosFin 31) f1421 := by
  apply lratCheckerSound f1421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1421
  · intro a ha; simp [p1421] at ha; subst a; trivial
  · exact checked1421
theorem derived1421 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1421 := by
  apply localUnsat_implies_entails f1421 [c1286, c502, c191, c137, c84] c1421 unsat1421 (by rfl) a
  have h0 : Entails.eval a c1286 := derived1286 a h
  have h1 : Entails.eval a c502 := h 501 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1422 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1422 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c688, some c129, some c590, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1422 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1422 : lratChecker f1422 p1422 = .success := by decide +kernel
theorem unsat1422 : Unsatisfiable (PosFin 31) f1422 := by
  apply lratCheckerSound f1422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1422
  · intro a ha; simp [p1422] at ha; subst a; trivial
  · exact checked1422
theorem derived1422 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1422 := by
  apply localUnsat_implies_entails f1422 [c688, c129, c590] c1422 unsat1422 (by rfl) a
  have h0 : Entails.eval a c688 := h 687 (by decide)
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c590 := h 589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1423 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1423 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1420, some c1421, some c1422, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1423 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1423 : lratChecker f1423 p1423 = .success := by decide +kernel
theorem unsat1423 : Unsatisfiable (PosFin 31) f1423 := by
  apply lratCheckerSound f1423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1423
  · intro a ha; simp [p1423] at ha; subst a; trivial
  · exact checked1423
theorem derived1423 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1423 := by
  apply localUnsat_implies_entails f1423 [c1420, c1421, c1422] c1423 unsat1423 (by rfl) a
  have h0 : Entails.eval a c1420 := derived1420 a h
  have h1 : Entails.eval a c1421 := derived1421 a h
  have h2 : Entails.eval a c1422 := derived1422 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1424 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1424 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1393, some c1418, some c1419, some c1423, some c763, some c570, some c1251, some c252, some c70, some c1272, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1424 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1424 : lratChecker f1424 p1424 = .success := by decide +kernel
theorem unsat1424 : Unsatisfiable (PosFin 31) f1424 := by
  apply lratCheckerSound f1424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1424
  · intro a ha; simp [p1424] at ha; subst a; trivial
  · exact checked1424
theorem derived1424 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1424 := by
  apply localUnsat_implies_entails f1424 [c1393, c1418, c1419, c1423, c763, c570, c1251, c252, c70, c1272] c1424 unsat1424 (by rfl) a
  have h0 : Entails.eval a c1393 := derived1393 a h
  have h1 : Entails.eval a c1418 := derived1418 a h
  have h2 : Entails.eval a c1419 := derived1419 a h
  have h3 : Entails.eval a c1423 := derived1423 a h
  have h4 : Entails.eval a c763 := h 762 (by decide)
  have h5 : Entails.eval a c570 := h 569 (by decide)
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c1272 := derived1272 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1425 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1425 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1286, some c1421, some c682, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1425 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1425 : lratChecker f1425 p1425 = .success := by decide +kernel
theorem unsat1425 : Unsatisfiable (PosFin 31) f1425 := by
  apply lratCheckerSound f1425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1425
  · intro a ha; simp [p1425] at ha; subst a; trivial
  · exact checked1425
theorem derived1425 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1425 := by
  apply localUnsat_implies_entails f1425 [c1286, c1421, c682] c1425 unsat1425 (by rfl) a
  have h0 : Entails.eval a c1286 := derived1286 a h
  have h1 : Entails.eval a c1421 := derived1421 a h
  have h2 : Entails.eval a c682 := h 681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1426 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1418, some c1393, some c1419, some c1425, some c182, some c1424, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1426 : lratChecker f1426 p1426 = .success := by decide +kernel
theorem unsat1426 : Unsatisfiable (PosFin 31) f1426 := by
  apply lratCheckerSound f1426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1426
  · intro a ha; simp [p1426] at ha; subst a; trivial
  · exact checked1426
theorem derived1426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1426 := by
  apply localUnsat_implies_entails f1426 [c1418, c1393, c1419, c1425, c182, c1424] c1426 unsat1426 (by rfl) a
  have h0 : Entails.eval a c1418 := derived1418 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1419 := derived1419 a h
  have h3 : Entails.eval a c1425 := derived1425 a h
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c1424 := derived1424 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1427 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c503, some c1249, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1427 : lratChecker f1427 p1427 = .success := by decide +kernel
theorem unsat1427 : Unsatisfiable (PosFin 31) f1427 := by
  apply lratCheckerSound f1427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1427
  · intro a ha; simp [p1427] at ha; subst a; trivial
  · exact checked1427
theorem derived1427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1427 := by
  apply localUnsat_implies_entails f1427 [c503, c1249] c1427 unsat1427 (by rfl) a
  have h0 : Entails.eval a c503 := h 502 (by decide)
  have h1 : Entails.eval a c1249 := derived1249 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1428 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1393, some c1418, some c1426, some c1208, some c1425, some c1422, some c1221, some c1427, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1428 : lratChecker f1428 p1428 = .success := by decide +kernel
theorem unsat1428 : Unsatisfiable (PosFin 31) f1428 := by
  apply lratCheckerSound f1428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1428
  · intro a ha; simp [p1428] at ha; subst a; trivial
  · exact checked1428
theorem derived1428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1428 := by
  apply localUnsat_implies_entails f1428 [c1393, c1418, c1426, c1208, c1425, c1422, c1221, c1427] c1428 unsat1428 (by rfl) a
  have h0 : Entails.eval a c1393 := derived1393 a h
  have h1 : Entails.eval a c1418 := derived1418 a h
  have h2 : Entails.eval a c1426 := derived1426 a h
  have h3 : Entails.eval a c1208 := derived1208 a h
  have h4 : Entails.eval a c1425 := derived1425 a h
  have h5 : Entails.eval a c1422 := derived1422 a h
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c1427 := derived1427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1429 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c53, some c552, some c746, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1429 : lratChecker f1429 p1429 = .success := by decide +kernel
theorem unsat1429 : Unsatisfiable (PosFin 31) f1429 := by
  apply lratCheckerSound f1429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1429
  · intro a ha; simp [p1429] at ha; subst a; trivial
  · exact checked1429
theorem derived1429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1429 := by
  apply localUnsat_implies_entails f1429 [c1428, c53, c552, c746] c1429 unsat1429 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c552 := h 551 (by decide)
  have h3 : Entails.eval a c746 := h 745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1430 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1205, some c1366, some c1429, some c401, some c564, some c432, some c758, some c1240, some c166, some c1140, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1430 : lratChecker f1430 p1430 = .success := by decide +kernel
theorem unsat1430 : Unsatisfiable (PosFin 31) f1430 := by
  apply lratCheckerSound f1430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1430
  · intro a ha; simp [p1430] at ha; subst a; trivial
  · exact checked1430
theorem derived1430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1430 := by
  apply localUnsat_implies_entails f1430 [c1428, c1205, c1366, c1429, c401, c564, c432, c758, c1240, c166, c1140] c1430 unsat1430 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1429 := derived1429 a h
  have h4 : Entails.eval a c401 := h 400 (by decide)
  have h5 : Entails.eval a c564 := h 563 (by decide)
  have h6 : Entails.eval a c432 := h 431 (by decide)
  have h7 : Entails.eval a c758 := h 757 (by decide)
  have h8 : Entails.eval a c1240 := derived1240 a h
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c1140 := derived1140 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1431 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1205, some c1393, some c1366, some c253, some c254, some c744, some c15, some c553, some c743, some c294, some c281, some c250, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1431 : lratChecker f1431 p1431 = .success := by decide +kernel
theorem unsat1431 : Unsatisfiable (PosFin 31) f1431 := by
  apply lratCheckerSound f1431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1431
  · intro a ha; simp [p1431] at ha; subst a; trivial
  · exact checked1431
theorem derived1431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1431 := by
  apply localUnsat_implies_entails f1431 [c1428, c1205, c1393, c1366, c253, c254, c744, c15, c553, c743, c294, c281, c250] c1431 unsat1431 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c744 := h 743 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c553 := h 552 (by decide)
  have h9 : Entails.eval a c743 := h 742 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1432 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1393, some c1430, some c1431, some c1221, some c646, some c53, some c747, some c553, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1432 : lratChecker f1432 p1432 = .success := by decide +kernel
theorem unsat1432 : Unsatisfiable (PosFin 31) f1432 := by
  apply lratCheckerSound f1432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1432
  · intro a ha; simp [p1432] at ha; subst a; trivial
  · exact checked1432
theorem derived1432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1432 := by
  apply localUnsat_implies_entails f1432 [c1428, c1393, c1430, c1431, c1221, c646, c53, c747, c553] c1432 unsat1432 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1430 := derived1430 a h
  have h3 : Entails.eval a c1431 := derived1431 a h
  have h4 : Entails.eval a c1221 := derived1221 a h
  have h5 : Entails.eval a c646 := h 645 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c747 := h 746 (by decide)
  have h8 : Entails.eval a c553 := h 552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1433 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1393, some c1221, some c646, some c53, some c747, some c553, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1433 : lratChecker f1433 p1433 = .success := by decide +kernel
theorem unsat1433 : Unsatisfiable (PosFin 31) f1433 := by
  apply lratCheckerSound f1433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1433
  · intro a ha; simp [p1433] at ha; subst a; trivial
  · exact checked1433
theorem derived1433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1433 := by
  apply localUnsat_implies_entails f1433 [c1428, c1393, c1221, c646, c53, c747, c553] c1433 unsat1433 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c646 := h 645 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c747 := h 746 (by decide)
  have h6 : Entails.eval a c553 := h 552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1434 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1205, some c1393, some c1366, some c1433, some c253, some c254, some c1413, some c553, some c743, some c1224, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1434 : lratChecker f1434 p1434 = .success := by decide +kernel
theorem unsat1434 : Unsatisfiable (PosFin 31) f1434 := by
  apply lratCheckerSound f1434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1434
  · intro a ha; simp [p1434] at ha; subst a; trivial
  · exact checked1434
theorem derived1434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1434 := by
  apply localUnsat_implies_entails f1434 [c1428, c1205, c1393, c1366, c1433, c253, c254, c1413, c553, c743, c1224] c1434 unsat1434 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c1433 := derived1433 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c254 := h 253 (by decide)
  have h7 : Entails.eval a c1413 := derived1413 a h
  have h8 : Entails.eval a c553 := h 552 (by decide)
  have h9 : Entails.eval a c743 := h 742 (by decide)
  have h10 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1435 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c1432, some c1428, some c1393, some c1366, some c254, some c15, some c522, some c497, some c1292, some c43, some c526, some c707, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1435 : lratChecker f1435 p1435 = .success := by decide +kernel
theorem unsat1435 : Unsatisfiable (PosFin 31) f1435 := by
  apply lratCheckerSound f1435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1435
  · intro a ha; simp [p1435] at ha; subst a; trivial
  · exact checked1435
theorem derived1435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1435 := by
  apply localUnsat_implies_entails f1435 [c53, c1432, c1428, c1393, c1366, c254, c15, c522, c497, c1292, c43, c526, c707] c1435 unsat1435 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1428 := derived1428 a h
  have h3 : Entails.eval a c1393 := derived1393 a h
  have h4 : Entails.eval a c1366 := derived1366 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c522 := h 521 (by decide)
  have h8 : Entails.eval a c497 := h 496 (by decide)
  have h9 : Entails.eval a c1292 := derived1292 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c526 := h 525 (by decide)
  have h12 : Entails.eval a c707 := h 706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1436 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1432, some c1366, some c1428, some c22, some c1435, some c129, some c514, some c26, some c138, some c85, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1436 : lratChecker f1436 p1436 = .success := by decide +kernel
theorem unsat1436 : Unsatisfiable (PosFin 31) f1436 := by
  apply lratCheckerSound f1436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1436
  · intro a ha; simp [p1436] at ha; subst a; trivial
  · exact checked1436
theorem derived1436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1436 := by
  apply localUnsat_implies_entails f1436 [c1432, c1366, c1428, c22, c1435, c129, c514, c26, c138, c85] c1436 unsat1436 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1366 := derived1366 a h
  have h2 : Entails.eval a c1428 := derived1428 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1435 := derived1435 a h
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c514 := h 513 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1437 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1428, some c22, some c129, some c182, some c400, some c138, some c142, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1437 : lratChecker f1437 p1437 = .success := by decide +kernel
theorem unsat1437 : Unsatisfiable (PosFin 31) f1437 := by
  apply lratCheckerSound f1437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1437
  · intro a ha; simp [p1437] at ha; subst a; trivial
  · exact checked1437
theorem derived1437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1437 := by
  apply localUnsat_implies_entails f1437 [c1366, c1428, c22, c129, c182, c400, c138, c142] c1437 unsat1437 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1428 := derived1428 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c400 := h 399 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1438 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1432, some c1428, some c1393, some c1366, some c1436, some c1437, some c254, some c553, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1438 : lratChecker f1438 p1438 = .success := by decide +kernel
theorem unsat1438 : Unsatisfiable (PosFin 31) f1438 := by
  apply lratCheckerSound f1438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1438
  · intro a ha; simp [p1438] at ha; subst a; trivial
  · exact checked1438
theorem derived1438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1438 := by
  apply localUnsat_implies_entails f1438 [c1432, c1428, c1393, c1366, c1436, c1437, c254, c553] c1438 unsat1438 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1428 := derived1428 a h
  have h2 : Entails.eval a c1393 := derived1393 a h
  have h3 : Entails.eval a c1366 := derived1366 a h
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c1437 := derived1437 a h
  have h6 : Entails.eval a c254 := h 253 (by decide)
  have h7 : Entails.eval a c553 := h 552 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1439 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1438, some c1434, some c1432, some c1428, some c1393, some c1366, some c325, some c1304, some c351, some c1209, some c1271, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1439 : lratChecker f1439 p1439 = .success := by decide +kernel
theorem unsat1439 : Unsatisfiable (PosFin 31) f1439 := by
  apply lratCheckerSound f1439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1439
  · intro a ha; simp [p1439] at ha; subst a; trivial
  · exact checked1439
theorem derived1439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1439 := by
  apply localUnsat_implies_entails f1439 [c1438, c1434, c1432, c1428, c1393, c1366, c325, c1304, c351, c1209, c1271] c1439 unsat1439 (by rfl) a
  have h0 : Entails.eval a c1438 := derived1438 a h
  have h1 : Entails.eval a c1434 := derived1434 a h
  have h2 : Entails.eval a c1432 := derived1432 a h
  have h3 : Entails.eval a c1428 := derived1428 a h
  have h4 : Entails.eval a c1393 := derived1393 a h
  have h5 : Entails.eval a c1366 := derived1366 a h
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c1304 := derived1304 a h
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c1209 := derived1209 a h
  have h10 : Entails.eval a c1271 := derived1271 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1440 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1428, some c1393, some c1366, some c1432, some c1434, some c1438, some c1439, some c53, some c265, some c646, some c170, some c563, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1440 : lratChecker f1440 p1440 = .success := by decide +kernel
theorem unsat1440 : Unsatisfiable (PosFin 31) f1440 := by
  apply lratCheckerSound f1440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1440
  · intro a ha; simp [p1440] at ha; subst a; trivial
  · exact checked1440
theorem derived1440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1440 := by
  apply localUnsat_implies_entails f1440 [c1428, c1393, c1366, c1432, c1434, c1438, c1439, c53, c265, c646, c170, c563] c1440 unsat1440 (by rfl) a
  have h0 : Entails.eval a c1428 := derived1428 a h
  have h1 : Entails.eval a c1393 := derived1393 a h
  have h2 : Entails.eval a c1366 := derived1366 a h
  have h3 : Entails.eval a c1432 := derived1432 a h
  have h4 : Entails.eval a c1434 := derived1434 a h
  have h5 : Entails.eval a c1438 := derived1438 a h
  have h6 : Entails.eval a c1439 := derived1439 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c646 := h 645 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c563 := h 562 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1441 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1366, some c1428, some c1205, some c22, some c1440, some c1208, some c1367, some c50, some c138, some c192, some c85, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1441 : lratChecker f1441 p1441 = .success := by decide +kernel
theorem unsat1441 : Unsatisfiable (PosFin 31) f1441 := by
  apply lratCheckerSound f1441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1441
  · intro a ha; simp [p1441] at ha; subst a; trivial
  · exact checked1441
theorem derived1441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1441 := by
  apply localUnsat_implies_entails f1441 [c1366, c1428, c1205, c22, c1440, c1208, c1367, c50, c138, c192, c85] c1441 unsat1441 (by rfl) a
  have h0 : Entails.eval a c1366 := derived1366 a h
  have h1 : Entails.eval a c1428 := derived1428 a h
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c1440 := derived1440 a h
  have h5 : Entails.eval a c1208 := derived1208 a h
  have h6 : Entails.eval a c1367 := derived1367 a h
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1442 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c135, some c563, some c1270, some c901, some c546, some c1239, some c110, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1442 : lratChecker f1442 p1442 = .success := by decide +kernel
theorem unsat1442 : Unsatisfiable (PosFin 31) f1442 := by
  apply lratCheckerSound f1442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1442
  · intro a ha; simp [p1442] at ha; subst a; trivial
  · exact checked1442
theorem derived1442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1442 := by
  apply localUnsat_implies_entails f1442 [c1441, c135, c563, c1270, c901, c546, c1239, c110] c1442 unsat1442 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c563 := h 562 (by decide)
  have h3 : Entails.eval a c1270 := derived1270 a h
  have h4 : Entails.eval a c901 := h 900 (by decide)
  have h5 : Entails.eval a c546 := h 545 (by decide)
  have h6 : Entails.eval a c1239 := derived1239 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1443 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c370, some c69, some c749, some c905, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1443 : lratChecker f1443 p1443 = .success := by decide +kernel
theorem unsat1443 : Unsatisfiable (PosFin 31) f1443 := by
  apply lratCheckerSound f1443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1443
  · intro a ha; simp [p1443] at ha; subst a; trivial
  · exact checked1443
theorem derived1443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1443 := by
  apply localUnsat_implies_entails f1443 [c1441, c370, c69, c749, c905] c1443 unsat1443 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c749 := h 748 (by decide)
  have h4 : Entails.eval a c905 := h 904 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1444 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1239, some c79, some c188, some c1203, some c1443, some c1293, some c396, some c640, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1444 : lratChecker f1444 p1444 = .success := by decide +kernel
theorem unsat1444 : Unsatisfiable (PosFin 31) f1444 := by
  apply lratCheckerSound f1444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1444
  · intro a ha; simp [p1444] at ha; subst a; trivial
  · exact checked1444
theorem derived1444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1444 := by
  apply localUnsat_implies_entails f1444 [c1441, c1239, c79, c188, c1203, c1443, c1293, c396, c640] c1444 unsat1444 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1239 := derived1239 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c1203 := derived1203 a h
  have h5 : Entails.eval a c1443 := derived1443 a h
  have h6 : Entails.eval a c1293 := derived1293 a h
  have h7 : Entails.eval a c396 := h 395 (by decide)
  have h8 : Entails.eval a c640 := h 639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1445 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1444, some c1246, some c79, some c81, some c134, some c769, some c471, some c30, some c39, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1445 : lratChecker f1445 p1445 = .success := by decide +kernel
theorem unsat1445 : Unsatisfiable (PosFin 31) f1445 := by
  apply lratCheckerSound f1445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1445
  · intro a ha; simp [p1445] at ha; subst a; trivial
  · exact checked1445
theorem derived1445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1445 := by
  apply localUnsat_implies_entails f1445 [c1441, c1444, c1246, c79, c81, c134, c769, c471, c30, c39] c1445 unsat1445 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c769 := h 768 (by decide)
  have h7 : Entails.eval a c471 := h 470 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1446 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1302, some c30, some c246, some c134, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1446 : lratChecker f1446 p1446 = .success := by decide +kernel
theorem unsat1446 : Unsatisfiable (PosFin 31) f1446 := by
  apply lratCheckerSound f1446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1446
  · intro a ha; simp [p1446] at ha; subst a; trivial
  · exact checked1446
theorem derived1446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1446 := by
  apply localUnsat_implies_entails f1446 [c1441, c1302, c30, c246, c134] c1446 unsat1446 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1302 := derived1302 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1447 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1442, some c1445, some c312, some c352, some c31, some c1446, some c345, some c305, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1447 : lratChecker f1447 p1447 = .success := by decide +kernel
theorem unsat1447 : Unsatisfiable (PosFin 31) f1447 := by
  apply lratCheckerSound f1447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1447
  · intro a ha; simp [p1447] at ha; subst a; trivial
  · exact checked1447
theorem derived1447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1447 := by
  apply localUnsat_implies_entails f1447 [c1442, c1445, c312, c352, c31, c1446, c345, c305] c1447 unsat1447 (by rfl) a
  have h0 : Entails.eval a c1442 := derived1442 a h
  have h1 : Entails.eval a c1445 := derived1445 a h
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c1446 := derived1446 a h
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1448 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨28, by decide⟩, false), (⟨1, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1239, some c64, some c188, some c21, some c202, some c138, some c85, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1448 : lratChecker f1448 p1448 = .success := by decide +kernel
theorem unsat1448 : Unsatisfiable (PosFin 31) f1448 := by
  apply lratCheckerSound f1448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1448
  · intro a ha; simp [p1448] at ha; subst a; trivial
  · exact checked1448
theorem derived1448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1448 := by
  apply localUnsat_implies_entails f1448 [c1441, c1239, c64, c188, c21, c202, c138, c85] c1448 unsat1448 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1239 := derived1239 a h
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1449 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, false), (⟨1, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1448, some c756, some c30, some c257, some c312, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1449 : lratChecker f1449 p1449 = .success := by decide +kernel
theorem unsat1449 : Unsatisfiable (PosFin 31) f1449 := by
  apply lratCheckerSound f1449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1449
  · intro a ha; simp [p1449] at ha; subst a; trivial
  · exact checked1449
theorem derived1449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1449 := by
  apply localUnsat_implies_entails f1449 [c1448, c756, c30, c257, c312] c1449 unsat1449 (by rfl) a
  have h0 : Entails.eval a c1448 := derived1448 a h
  have h1 : Entails.eval a c756 := h 755 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1450 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c258, some c161, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1450 : lratChecker f1450 p1450 = .success := by decide +kernel
theorem unsat1450 : Unsatisfiable (PosFin 31) f1450 := by
  apply lratCheckerSound f1450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1450
  · intro a ha; simp [p1450] at ha; subst a; trivial
  · exact checked1450
theorem derived1450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1450 := by
  apply localUnsat_implies_entails f1450 [c1441, c258, c161] c1450 unsat1450 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1451 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c30, some c1278, some c157, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1451 : lratChecker f1451 p1451 = .success := by decide +kernel
theorem unsat1451 : Unsatisfiable (PosFin 31) f1451 := by
  apply lratCheckerSound f1451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1451
  · intro a ha; simp [p1451] at ha; subst a; trivial
  · exact checked1451
theorem derived1451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1451 := by
  apply localUnsat_implies_entails f1451 [c30, c1278, c157] c1451 unsat1451 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c1278 := derived1278 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1452 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1452 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1450, some c1449, some c213, some c419, some c1451, some c672, some c107, some c1323, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1452 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1452 : lratChecker f1452 p1452 = .success := by decide +kernel
theorem unsat1452 : Unsatisfiable (PosFin 31) f1452 := by
  apply lratCheckerSound f1452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1452
  · intro a ha; simp [p1452] at ha; subst a; trivial
  · exact checked1452
theorem derived1452 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1452 := by
  apply localUnsat_implies_entails f1452 [c1441, c1450, c1449, c213, c419, c1451, c672, c107, c1323] c1452 unsat1452 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1450 := derived1450 a h
  have h2 : Entails.eval a c1449 := derived1449 a h
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c419 := h 418 (by decide)
  have h5 : Entails.eval a c1451 := derived1451 a h
  have h6 : Entails.eval a c672 := h 671 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c1323 := derived1323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1453 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1453 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c672, some c107, some c951, some c700, some c902, some c140, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1453 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1453 : lratChecker f1453 p1453 = .success := by decide +kernel
theorem unsat1453 : Unsatisfiable (PosFin 31) f1453 := by
  apply lratCheckerSound f1453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1453
  · intro a ha; simp [p1453] at ha; subst a; trivial
  · exact checked1453
theorem derived1453 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1453 := by
  apply localUnsat_implies_entails f1453 [c1441, c672, c107, c951, c700, c902, c140] c1453 unsat1453 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c672 := h 671 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c951 := derived951 a h
  have h4 : Entails.eval a c700 := h 699 (by decide)
  have h5 : Entails.eval a c902 := h 901 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1454 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1454 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1450, some c1452, some c1447, some c1453, some c30, some c752, some c303, some c349, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1454 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1454 : lratChecker f1454 p1454 = .success := by decide +kernel
theorem unsat1454 : Unsatisfiable (PosFin 31) f1454 := by
  apply lratCheckerSound f1454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1454
  · intro a ha; simp [p1454] at ha; subst a; trivial
  · exact checked1454
theorem derived1454 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1454 := by
  apply localUnsat_implies_entails f1454 [c1441, c1450, c1452, c1447, c1453, c30, c752, c303, c349] c1454 unsat1454 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1450 := derived1450 a h
  have h2 : Entails.eval a c1452 := derived1452 a h
  have h3 : Entails.eval a c1447 := derived1447 a h
  have h4 : Entails.eval a c1453 := derived1453 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c752 := h 751 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1455 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1455 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c30, some c726, some c52, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1455 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1455 : lratChecker f1455 p1455 = .success := by decide +kernel
theorem unsat1455 : Unsatisfiable (PosFin 31) f1455 := by
  apply lratCheckerSound f1455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1455
  · intro a ha; simp [p1455] at ha; subst a; trivial
  · exact checked1455
theorem derived1455 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1455 := by
  apply localUnsat_implies_entails f1455 [c30, c726, c52] c1455 unsat1455 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c726 := h 725 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1456 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1456 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c356, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1456 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1456 : lratChecker f1456 p1456 = .success := by decide +kernel
theorem unsat1456 : Unsatisfiable (PosFin 31) f1456 := by
  apply lratCheckerSound f1456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1456
  · intro a ha; simp [p1456] at ha; subst a; trivial
  · exact checked1456
theorem derived1456 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1456 := by
  apply localUnsat_implies_entails f1456 [c3, c356] c1456 unsat1456 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1457 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1457 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1454, some c1450, some c1447, some c1455, some c1456, some c31, some c1296, some c65, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1457 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1457 : lratChecker f1457 p1457 = .success := by decide +kernel
theorem unsat1457 : Unsatisfiable (PosFin 31) f1457 := by
  apply lratCheckerSound f1457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1457
  · intro a ha; simp [p1457] at ha; subst a; trivial
  · exact checked1457
theorem derived1457 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1457 := by
  apply localUnsat_implies_entails f1457 [c1441, c1454, c1450, c1447, c1455, c1456, c31, c1296, c65] c1457 unsat1457 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1454 := derived1454 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c1447 := derived1447 a h
  have h4 : Entails.eval a c1455 := derived1455 a h
  have h5 : Entails.eval a c1456 := derived1456 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c1296 := derived1296 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1458 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1458 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1450, some c1454, some c1457, some c727, some c535, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1458 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1458 : lratChecker f1458 p1458 = .success := by decide +kernel
theorem unsat1458 : Unsatisfiable (PosFin 31) f1458 := by
  apply lratCheckerSound f1458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1458
  · intro a ha; simp [p1458] at ha; subst a; trivial
  · exact checked1458
theorem derived1458 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1458 := by
  apply localUnsat_implies_entails f1458 [c1450, c1454, c1457, c727, c535] c1458 unsat1458 (by rfl) a
  have h0 : Entails.eval a c1450 := derived1450 a h
  have h1 : Entails.eval a c1454 := derived1454 a h
  have h2 : Entails.eval a c1457 := derived1457 a h
  have h3 : Entails.eval a c727 := h 726 (by decide)
  have h4 : Entails.eval a c535 := h 534 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1459 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1459 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c308, some c1234, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1459 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1459 : lratChecker f1459 p1459 = .success := by decide +kernel
theorem unsat1459 : Unsatisfiable (PosFin 31) f1459 := by
  apply lratCheckerSound f1459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1459
  · intro a ha; simp [p1459] at ha; subst a; trivial
  · exact checked1459
theorem derived1459 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1459 := by
  apply localUnsat_implies_entails f1459 [c308, c1234] c1459 unsat1459 (by rfl) a
  have h0 : Entails.eval a c308 := h 307 (by decide)
  have h1 : Entails.eval a c1234 := derived1234 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1460 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1460 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1458, some c1459, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1460 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1460 : lratChecker f1460 p1460 = .success := by decide +kernel
theorem unsat1460 : Unsatisfiable (PosFin 31) f1460 := by
  apply lratCheckerSound f1460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1460
  · intro a ha; simp [p1460] at ha; subst a; trivial
  · exact checked1460
theorem derived1460 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1460 := by
  apply localUnsat_implies_entails f1460 [c1458, c1459] c1460 unsat1460 (by rfl) a
  have h0 : Entails.eval a c1458 := derived1458 a h
  have h1 : Entails.eval a c1459 := derived1459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1461 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1461 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c970, some c15, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1461 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1461 : lratChecker f1461 p1461 = .success := by decide +kernel
theorem unsat1461 : Unsatisfiable (PosFin 31) f1461 := by
  apply lratCheckerSound f1461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1461
  · intro a ha; simp [p1461] at ha; subst a; trivial
  · exact checked1461
theorem derived1461 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1461 := by
  apply localUnsat_implies_entails f1461 [c1441, c970, c15] c1461 unsat1461 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c970 := derived970 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1462 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1462 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1460, some c1450, some c52, some c157, some c35, some c257, some c1058, some c1461, some c1257, some c412, some c1278, some c305, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1462 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1462 : lratChecker f1462 p1462 = .success := by decide +kernel
theorem unsat1462 : Unsatisfiable (PosFin 31) f1462 := by
  apply lratCheckerSound f1462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1462
  · intro a ha; simp [p1462] at ha; subst a; trivial
  · exact checked1462
theorem derived1462 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1462 := by
  apply localUnsat_implies_entails f1462 [c1441, c1460, c1450, c52, c157, c35, c257, c1058, c1461, c1257, c412, c1278, c305] c1462 unsat1462 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c1058 := derived1058 a h
  have h8 : Entails.eval a c1461 := derived1461 a h
  have h9 : Entails.eval a c1257 := derived1257 a h
  have h10 : Entails.eval a c412 := h 411 (by decide)
  have h11 : Entails.eval a c1278 := derived1278 a h
  have h12 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1463 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1463 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1460, some c1450, some c1462, some c355, some c247, some c45, some c809, some c138, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1463 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1463 : lratChecker f1463 p1463 = .success := by decide +kernel
theorem unsat1463 : Unsatisfiable (PosFin 31) f1463 := by
  apply lratCheckerSound f1463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1463
  · intro a ha; simp [p1463] at ha; subst a; trivial
  · exact checked1463
theorem derived1463 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1463 := by
  apply localUnsat_implies_entails f1463 [c1460, c1450, c1462, c355, c247, c45, c809, c138] c1463 unsat1463 (by rfl) a
  have h0 : Entails.eval a c1460 := derived1460 a h
  have h1 : Entails.eval a c1450 := derived1450 a h
  have h2 : Entails.eval a c1462 := derived1462 a h
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c809 := h 808 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1464 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1464 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1203, some c45, some c809, some c843, some c86, some c488, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1464 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1464 : lratChecker f1464 p1464 = .success := by decide +kernel
theorem unsat1464 : Unsatisfiable (PosFin 31) f1464 := by
  apply lratCheckerSound f1464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1464
  · intro a ha; simp [p1464] at ha; subst a; trivial
  · exact checked1464
theorem derived1464 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1464 := by
  apply localUnsat_implies_entails f1464 [c1203, c45, c809, c843, c86, c488] c1464 unsat1464 (by rfl) a
  have h0 : Entails.eval a c1203 := derived1203 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c809 := h 808 (by decide)
  have h3 : Entails.eval a c843 := h 842 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c488 := h 487 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1465 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1465 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1464, some c79, some c189, some c1204, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1465 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1465 : lratChecker f1465 p1465 = .success := by decide +kernel
theorem unsat1465 : Unsatisfiable (PosFin 31) f1465 := by
  apply lratCheckerSound f1465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1465
  · intro a ha; simp [p1465] at ha; subst a; trivial
  · exact checked1465
theorem derived1465 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1465 := by
  apply localUnsat_implies_entails f1465 [c1441, c1464, c79, c189, c1204] c1465 unsat1465 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1464 := derived1464 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1204 := derived1204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1466 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1466 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c355, some c1465, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1466 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1466 : lratChecker f1466 p1466 = .success := by decide +kernel
theorem unsat1466 : Unsatisfiable (PosFin 31) f1466 := by
  apply lratCheckerSound f1466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1466
  · intro a ha; simp [p1466] at ha; subst a; trivial
  · exact checked1466
theorem derived1466 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1466 := by
  apply localUnsat_implies_entails f1466 [c355, c1465] c1466 unsat1466 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c1465 := derived1465 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1467 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1467 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c35, some c534, some c341, some c412, some c216, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1467 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1467 : lratChecker f1467 p1467 = .success := by decide +kernel
theorem unsat1467 : Unsatisfiable (PosFin 31) f1467 := by
  apply lratCheckerSound f1467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1467
  · intro a ha; simp [p1467] at ha; subst a; trivial
  · exact checked1467
theorem derived1467 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1467 := by
  apply localUnsat_implies_entails f1467 [c1441, c35, c534, c341, c412, c216] c1467 unsat1467 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c534 := h 533 (by decide)
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c412 := h 411 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1468 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1468 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1460, some c1450, some c1463, some c1466, some c52, some c1467, some c421, some c135, some c1310, some c1240, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1468 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1468 : lratChecker f1468 p1468 = .success := by decide +kernel
theorem unsat1468 : Unsatisfiable (PosFin 31) f1468 := by
  apply lratCheckerSound f1468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1468
  · intro a ha; simp [p1468] at ha; subst a; trivial
  · exact checked1468
theorem derived1468 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1468 := by
  apply localUnsat_implies_entails f1468 [c1441, c1460, c1450, c1463, c1466, c52, c1467, c421, c135, c1310, c1240] c1468 unsat1468 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c1463 := derived1463 a h
  have h4 : Entails.eval a c1466 := derived1466 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c1467 := derived1467 a h
  have h7 : Entails.eval a c421 := h 420 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c1310 := derived1310 a h
  have h10 : Entails.eval a c1240 := derived1240 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1469 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1469 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c52, some c3, some c371, some c1240, some c1254, some c79, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1469 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1469 : lratChecker f1469 p1469 = .success := by decide +kernel
theorem unsat1469 : Unsatisfiable (PosFin 31) f1469 := by
  apply lratCheckerSound f1469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1469
  · intro a ha; simp [p1469] at ha; subst a; trivial
  · exact checked1469
theorem derived1469 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1469 := by
  apply localUnsat_implies_entails f1469 [c1441, c52, c3, c371, c1240, c1254, c79] c1469 unsat1469 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c1240 := derived1240 a h
  have h5 : Entails.eval a c1254 := derived1254 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1470 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1470 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1460, some c1450, some c3, some c52, some c35, some c1469, some c66, some c69, some c1254, some c1313, some c748, some c1058, some c567, some c216, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1470 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1470 : lratChecker f1470 p1470 = .success := by decide +kernel
theorem unsat1470 : Unsatisfiable (PosFin 31) f1470 := by
  apply lratCheckerSound f1470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1470
  · intro a ha; simp [p1470] at ha; subst a; trivial
  · exact checked1470
theorem derived1470 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1470 := by
  apply localUnsat_implies_entails f1470 [c1441, c1460, c1450, c3, c52, c35, c1469, c66, c69, c1254, c1313, c748, c1058, c567, c216] c1470 unsat1470 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c1469 := derived1469 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c1254 := derived1254 a h
  have h10 : Entails.eval a c1313 := derived1313 a h
  have h11 : Entails.eval a c748 := h 747 (by decide)
  have h12 : Entails.eval a c1058 := derived1058 a h
  have h13 : Entails.eval a c567 := h 566 (by decide)
  have h14 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1471 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1471 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c327, some c35, some c353, some c66, some c69, some c722, some c1313, some c253, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1471 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1471 : lratChecker f1471 p1471 = .success := by decide +kernel
theorem unsat1471 : Unsatisfiable (PosFin 31) f1471 := by
  apply lratCheckerSound f1471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1471
  · intro a ha; simp [p1471] at ha; subst a; trivial
  · exact checked1471
theorem derived1471 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1471 := by
  apply localUnsat_implies_entails f1471 [c1441, c327, c35, c353, c66, c69, c722, c1313, c253] c1471 unsat1471 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c722 := h 721 (by decide)
  have h7 : Entails.eval a c1313 := derived1313 a h
  have h8 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1472 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1472 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1468, some c1470, some c1460, some c1450, some c1471, some c309, some c254, some c7, some c326, some c766, some c253, some c1247, some c728, some c954, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1472 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1472 : lratChecker f1472 p1472 = .success := by decide +kernel
theorem unsat1472 : Unsatisfiable (PosFin 31) f1472 := by
  apply lratCheckerSound f1472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1472
  · intro a ha; simp [p1472] at ha; subst a; trivial
  · exact checked1472
theorem derived1472 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1472 := by
  apply localUnsat_implies_entails f1472 [c1441, c1468, c1470, c1460, c1450, c1471, c309, c254, c7, c326, c766, c253, c1247, c728, c954] c1472 unsat1472 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1468 := derived1468 a h
  have h2 : Entails.eval a c1470 := derived1470 a h
  have h3 : Entails.eval a c1460 := derived1460 a h
  have h4 : Entails.eval a c1450 := derived1450 a h
  have h5 : Entails.eval a c1471 := derived1471 a h
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c766 := h 765 (by decide)
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c1247 := derived1247 a h
  have h13 : Entails.eval a c728 := h 727 (by decide)
  have h14 : Entails.eval a c954 := derived954 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1473 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1473 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1460, some c1450, some c1468, some c1470, some c1472, some c371, some c533, some c241, some c348, some c19, some c196, some c103, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1473 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1473 : lratChecker f1473 p1473 = .success := by decide +kernel
theorem unsat1473 : Unsatisfiable (PosFin 31) f1473 := by
  apply lratCheckerSound f1473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1473
  · intro a ha; simp [p1473] at ha; subst a; trivial
  · exact checked1473
theorem derived1473 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1473 := by
  apply localUnsat_implies_entails f1473 [c1441, c1460, c1450, c1468, c1470, c1472, c371, c533, c241, c348, c19, c196, c103] c1473 unsat1473 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c1468 := derived1468 a h
  have h4 : Entails.eval a c1470 := derived1470 a h
  have h5 : Entails.eval a c1472 := derived1472 a h
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c533 := h 532 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1474 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1474 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c31, some c30, some c305, some c1053, some c65, some c1317, some c110, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1474 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1474 : lratChecker f1474 p1474 = .success := by decide +kernel
theorem unsat1474 : Unsatisfiable (PosFin 31) f1474 := by
  apply lratCheckerSound f1474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1474
  · intro a ha; simp [p1474] at ha; subst a; trivial
  · exact checked1474
theorem derived1474 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1474 := by
  apply localUnsat_implies_entails f1474 [c1441, c31, c30, c305, c1053, c65, c1317, c110] c1474 unsat1474 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c1053 := derived1053 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c1317 := derived1317 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1475 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1475 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c305, some c65, some c1299, some c851, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1475 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1475 : lratChecker f1475 p1475 = .success := by decide +kernel
theorem unsat1475 : Unsatisfiable (PosFin 31) f1475 := by
  apply lratCheckerSound f1475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1475
  · intro a ha; simp [p1475] at ha; subst a; trivial
  · exact checked1475
theorem derived1475 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1475 := by
  apply localUnsat_implies_entails f1475 [c1441, c305, c65, c1299, c851] c1475 unsat1475 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c851 := h 850 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1476 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1476 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1450, some c1460, some c1473, some c1474, some c52, some c1470, some c35, some c1475, some c1322, some c1324, some c1278, some c299, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1476 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1476 : lratChecker f1476 p1476 = .success := by decide +kernel
theorem unsat1476 : Unsatisfiable (PosFin 31) f1476 := by
  apply lratCheckerSound f1476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1476
  · intro a ha; simp [p1476] at ha; subst a; trivial
  · exact checked1476
theorem derived1476 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1476 := by
  apply localUnsat_implies_entails f1476 [c1450, c1460, c1473, c1474, c52, c1470, c35, c1475, c1322, c1324, c1278, c299] c1476 unsat1476 (by rfl) a
  have h0 : Entails.eval a c1450 := derived1450 a h
  have h1 : Entails.eval a c1460 := derived1460 a h
  have h2 : Entails.eval a c1473 := derived1473 a h
  have h3 : Entails.eval a c1474 := derived1474 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c1470 := derived1470 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c1475 := derived1475 a h
  have h8 : Entails.eval a c1322 := derived1322 a h
  have h9 : Entails.eval a c1324 := derived1324 a h
  have h10 : Entails.eval a c1278 := derived1278 a h
  have h11 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1477 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1477 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c52, some c359, some c3, some c595, some c15, some c990, some c766, some c292, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1477 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1477 : lratChecker f1477 p1477 = .success := by decide +kernel
theorem unsat1477 : Unsatisfiable (PosFin 31) f1477 := by
  apply lratCheckerSound f1477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1477
  · intro a ha; simp [p1477] at ha; subst a; trivial
  · exact checked1477
theorem derived1477 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1477 := by
  apply localUnsat_implies_entails f1477 [c1441, c52, c359, c3, c595, c15, c990, c766, c292] c1477 unsat1477 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c595 := h 594 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c990 := derived990 a h
  have h7 : Entails.eval a c766 := h 765 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1478 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1478 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c292, some c253, some c257, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1478 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1478 : lratChecker f1478 p1478 = .success := by decide +kernel
theorem unsat1478 : Unsatisfiable (PosFin 31) f1478 := by
  apply lratCheckerSound f1478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1478
  · intro a ha; simp [p1478] at ha; subst a; trivial
  · exact checked1478
theorem derived1478 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1478 := by
  apply localUnsat_implies_entails f1478 [c292, c253, c257] c1478 unsat1478 (by rfl) a
  have h0 : Entails.eval a c292 := h 291 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1479 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1479 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c52, some c3, some c1478, some c710, some c521, some c1293, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1479 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1479 : lratChecker f1479 p1479 = .success := by decide +kernel
theorem unsat1479 : Unsatisfiable (PosFin 31) f1479 := by
  apply lratCheckerSound f1479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1479
  · intro a ha; simp [p1479] at ha; subst a; trivial
  · exact checked1479
theorem derived1479 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1479 := by
  apply localUnsat_implies_entails f1479 [c1441, c52, c3, c1478, c710, c521, c1293] c1479 unsat1479 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1478 := derived1478 a h
  have h4 : Entails.eval a c710 := h 709 (by decide)
  have h5 : Entails.eval a c521 := h 520 (by decide)
  have h6 : Entails.eval a c1293 := derived1293 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1480 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1480 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1477, some c52, some c669, some c302, some c627, some c73, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1480 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1480 : lratChecker f1480 p1480 = .success := by decide +kernel
theorem unsat1480 : Unsatisfiable (PosFin 31) f1480 := by
  apply lratCheckerSound f1480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1480
  · intro a ha; simp [p1480] at ha; subst a; trivial
  · exact checked1480
theorem derived1480 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1480 := by
  apply localUnsat_implies_entails f1480 [c1441, c1477, c52, c669, c302, c627, c73] c1480 unsat1480 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1477 := derived1477 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c669 := h 668 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c627 := h 626 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1481 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1481 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1476, some c1477, some c1479, some c1480, some c1299, some c39, some c667, some c631, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1481 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1481 : lratChecker f1481 p1481 = .success := by decide +kernel
theorem unsat1481 : Unsatisfiable (PosFin 31) f1481 := by
  apply lratCheckerSound f1481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1481
  · intro a ha; simp [p1481] at ha; subst a; trivial
  · exact checked1481
theorem derived1481 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1481 := by
  apply localUnsat_implies_entails f1481 [c1476, c1477, c1479, c1480, c1299, c39, c667, c631] c1481 unsat1481 (by rfl) a
  have h0 : Entails.eval a c1476 := derived1476 a h
  have h1 : Entails.eval a c1477 := derived1477 a h
  have h2 : Entails.eval a c1479 := derived1479 a h
  have h3 : Entails.eval a c1480 := derived1480 a h
  have h4 : Entails.eval a c1299 := derived1299 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c667 := h 666 (by decide)
  have h7 : Entails.eval a c631 := h 630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1482 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1482 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1476, some c52, some c359, some c1299, some c39, some c1320, some c667, some c340, some c630, some c909, some c571, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1482 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1482 : lratChecker f1482 p1482 = .success := by decide +kernel
theorem unsat1482 : Unsatisfiable (PosFin 31) f1482 := by
  apply lratCheckerSound f1482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1482
  · intro a ha; simp [p1482] at ha; subst a; trivial
  · exact checked1482
theorem derived1482 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1482 := by
  apply localUnsat_implies_entails f1482 [c1476, c52, c359, c1299, c39, c1320, c667, c340, c630, c909, c571] c1482 unsat1482 (by rfl) a
  have h0 : Entails.eval a c1476 := derived1476 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c1299 := derived1299 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c1320 := derived1320 a h
  have h6 : Entails.eval a c667 := h 666 (by decide)
  have h7 : Entails.eval a c340 := h 339 (by decide)
  have h8 : Entails.eval a c630 := h 629 (by decide)
  have h9 : Entails.eval a c909 := h 908 (by decide)
  have h10 : Entails.eval a c571 := h 570 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1483 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1483 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1481, some c52, some c1476, some c1482, some c302, some c134, some c847, some c573, some c911, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1483 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1483 : lratChecker f1483 p1483 = .success := by decide +kernel
theorem unsat1483 : Unsatisfiable (PosFin 31) f1483 := by
  apply lratCheckerSound f1483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1483
  · intro a ha; simp [p1483] at ha; subst a; trivial
  · exact checked1483
theorem derived1483 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1483 := by
  apply localUnsat_implies_entails f1483 [c1441, c1481, c52, c1476, c1482, c302, c134, c847, c573, c911] c1483 unsat1483 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1481 := derived1481 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c1476 := derived1476 a h
  have h4 : Entails.eval a c1482 := derived1482 a h
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c847 := h 846 (by decide)
  have h8 : Entails.eval a c573 := h 572 (by decide)
  have h9 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1484 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1484 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1476, some c1483, some c3, some c1478, some c1479, some c15, some c595, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1484 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1484 : lratChecker f1484 p1484 = .success := by decide +kernel
theorem unsat1484 : Unsatisfiable (PosFin 31) f1484 := by
  apply lratCheckerSound f1484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1484
  · intro a ha; simp [p1484] at ha; subst a; trivial
  · exact checked1484
theorem derived1484 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1484 := by
  apply localUnsat_implies_entails f1484 [c1441, c1476, c1483, c3, c1478, c1479, c15, c595] c1484 unsat1484 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1476 := derived1476 a h
  have h2 : Entails.eval a c1483 := derived1483 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1478 := derived1478 a h
  have h5 : Entails.eval a c1479 := derived1479 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c595 := h 594 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1485 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1485 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c591, some c594, some c573, some c769, some c134, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1485 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1485 : lratChecker f1485 p1485 = .success := by decide +kernel
theorem unsat1485 : Unsatisfiable (PosFin 31) f1485 := by
  apply lratCheckerSound f1485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1485
  · intro a ha; simp [p1485] at ha; subst a; trivial
  · exact checked1485
theorem derived1485 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1485 := by
  apply localUnsat_implies_entails f1485 [c1441, c591, c594, c573, c769, c134] c1485 unsat1485 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c591 := h 590 (by decide)
  have h2 : Entails.eval a c594 := h 593 (by decide)
  have h3 : Entails.eval a c573 := h 572 (by decide)
  have h4 : Entails.eval a c769 := h 768 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1486 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1486 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c352, some c1485, some c253, some c527, some c19, some c718, some c1246, some c107, some c1276, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1486 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1486 : lratChecker f1486 p1486 = .success := by decide +kernel
theorem unsat1486 : Unsatisfiable (PosFin 31) f1486 := by
  apply lratCheckerSound f1486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1486
  · intro a ha; simp [p1486] at ha; subst a; trivial
  · exact checked1486
theorem derived1486 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1486 := by
  apply localUnsat_implies_entails f1486 [c1441, c352, c1485, c253, c527, c19, c718, c1246, c107, c1276] c1486 unsat1486 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c527 := h 526 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c718 := h 717 (by decide)
  have h7 : Entails.eval a c1246 := derived1246 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c1276 := derived1276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1487 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1487 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1204, some c1246, some c216, some c65, some c1203, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1487 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1487 : lratChecker f1487 p1487 = .success := by decide +kernel
theorem unsat1487 : Unsatisfiable (PosFin 31) f1487 := by
  apply lratCheckerSound f1487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1487
  · intro a ha; simp [p1487] at ha; subst a; trivial
  · exact checked1487
theorem derived1487 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1487 := by
  apply localUnsat_implies_entails f1487 [c1441, c1204, c1246, c216, c65, c1203] c1487 unsat1487 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1488 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1488 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1487, some c79, some c527, some c66, some c76, some c571, some c808, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1488 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1488 : lratChecker f1488 p1488 = .success := by decide +kernel
theorem unsat1488 : Unsatisfiable (PosFin 31) f1488 := by
  apply lratCheckerSound f1488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1488
  · intro a ha; simp [p1488] at ha; subst a; trivial
  · exact checked1488
theorem derived1488 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1488 := by
  apply localUnsat_implies_entails f1488 [c1441, c1487, c79, c527, c66, c76, c571, c808] c1488 unsat1488 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1487 := derived1487 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c527 := h 526 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c571 := h 570 (by decide)
  have h7 : Entails.eval a c808 := h 807 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1489 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1489 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1203, some c1296, some c759, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1489 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1489 : lratChecker f1489 p1489 = .success := by decide +kernel
theorem unsat1489 : Unsatisfiable (PosFin 31) f1489 := by
  apply lratCheckerSound f1489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1489
  · intro a ha; simp [p1489] at ha; subst a; trivial
  · exact checked1489
theorem derived1489 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1489 := by
  apply localUnsat_implies_entails f1489 [c1441, c1203, c1296, c759] c1489 unsat1489 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1203 := derived1203 a h
  have h2 : Entails.eval a c1296 := derived1296 a h
  have h3 : Entails.eval a c759 := h 758 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1490 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1490 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1488, some c1489, some c79, some c628, some c666, some c65, some c1266, some c174, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1490 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1490 : lratChecker f1490 p1490 = .success := by decide +kernel
theorem unsat1490 : Unsatisfiable (PosFin 31) f1490 := by
  apply lratCheckerSound f1490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1490
  · intro a ha; simp [p1490] at ha; subst a; trivial
  · exact checked1490
theorem derived1490 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1490 := by
  apply localUnsat_implies_entails f1490 [c1441, c1488, c1489, c79, c628, c666, c65, c1266, c174] c1490 unsat1490 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1488 := derived1488 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c628 := h 627 (by decide)
  have h5 : Entails.eval a c666 := h 665 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1266 := derived1266 a h
  have h8 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1491 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1491 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1489, some c79, some c847, some c911, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1491 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1491 : lratChecker f1491 p1491 = .success := by decide +kernel
theorem unsat1491 : Unsatisfiable (PosFin 31) f1491 := by
  apply lratCheckerSound f1491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1491
  · intro a ha; simp [p1491] at ha; subst a; trivial
  · exact checked1491
theorem derived1491 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1491 := by
  apply localUnsat_implies_entails f1491 [c1441, c1489, c79, c847, c911] c1491 unsat1491 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c847 := h 846 (by decide)
  have h4 : Entails.eval a c911 := h 910 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1492 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1492 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1490, some c1491, some c1487, some c527, some c66, some c1279, some c418, some c899, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1492 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1492 : lratChecker f1492 p1492 = .success := by decide +kernel
theorem unsat1492 : Unsatisfiable (PosFin 31) f1492 := by
  apply lratCheckerSound f1492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1492
  · intro a ha; simp [p1492] at ha; subst a; trivial
  · exact checked1492
theorem derived1492 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1492 := by
  apply localUnsat_implies_entails f1492 [c1441, c1490, c1491, c1487, c527, c66, c1279, c418, c899] c1492 unsat1492 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1490 := derived1490 a h
  have h2 : Entails.eval a c1491 := derived1491 a h
  have h3 : Entails.eval a c1487 := derived1487 a h
  have h4 : Entails.eval a c527 := h 526 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c1279 := derived1279 a h
  have h7 : Entails.eval a c418 := h 417 (by decide)
  have h8 : Entails.eval a c899 := h 898 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1493 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1493 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1486, some c1492, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1493 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1493 : lratChecker f1493 p1493 = .success := by decide +kernel
theorem unsat1493 : Unsatisfiable (PosFin 31) f1493 := by
  apply lratCheckerSound f1493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1493
  · intro a ha; simp [p1493] at ha; subst a; trivial
  · exact checked1493
theorem derived1493 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1493 := by
  apply localUnsat_implies_entails f1493 [c1486, c1492] c1493 unsat1493 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1492 := derived1492 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1494 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1494 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1476, some c1484, some c31, some c1493, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1494 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1494 : lratChecker f1494 p1494 = .success := by decide +kernel
theorem unsat1494 : Unsatisfiable (PosFin 31) f1494 := by
  apply lratCheckerSound f1494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1494
  · intro a ha; simp [p1494] at ha; subst a; trivial
  · exact checked1494
theorem derived1494 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1494 := by
  apply localUnsat_implies_entails f1494 [c1476, c1484, c31, c1493] c1494 unsat1494 (by rfl) a
  have h0 : Entails.eval a c1476 := derived1476 a h
  have h1 : Entails.eval a c1484 := derived1484 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c1493 := derived1493 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1495 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1495 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c79, some c134, some c1203, some c1048, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1495 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1495 : lratChecker f1495 p1495 = .success := by decide +kernel
theorem unsat1495 : Unsatisfiable (PosFin 31) f1495 := by
  apply lratCheckerSound f1495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1495
  · intro a ha; simp [p1495] at ha; subst a; trivial
  · exact checked1495
theorem derived1495 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1495 := by
  apply localUnsat_implies_entails f1495 [c1441, c79, c134, c1203, c1048] c1495 unsat1495 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c1203 := derived1203 a h
  have h4 : Entails.eval a c1048 := derived1048 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1496 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1496 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1494, some c1459, some c1476, some c1466, some c1495, some c1204, some c420, some c216, some c1225, some c1203, some c1302, some c65, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1496 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1496 : lratChecker f1496 p1496 = .success := by decide +kernel
theorem unsat1496 : Unsatisfiable (PosFin 31) f1496 := by
  apply lratCheckerSound f1496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1496
  · intro a ha; simp [p1496] at ha; subst a; trivial
  · exact checked1496
theorem derived1496 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1496 := by
  apply localUnsat_implies_entails f1496 [c1441, c1494, c1459, c1476, c1466, c1495, c1204, c420, c216, c1225, c1203, c1302, c65] c1496 unsat1496 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1494 := derived1494 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c1476 := derived1476 a h
  have h4 : Entails.eval a c1466 := derived1466 a h
  have h5 : Entails.eval a c1495 := derived1495 a h
  have h6 : Entails.eval a c1204 := derived1204 a h
  have h7 : Entails.eval a c420 := h 419 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c1225 := derived1225 a h
  have h10 : Entails.eval a c1203 := derived1203 a h
  have h11 : Entails.eval a c1302 := derived1302 a h
  have h12 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1497 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1497 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1459, some c309, some c327, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1497 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1497 : lratChecker f1497 p1497 = .success := by decide +kernel
theorem unsat1497 : Unsatisfiable (PosFin 31) f1497 := by
  apply lratCheckerSound f1497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1497
  · intro a ha; simp [p1497] at ha; subst a; trivial
  · exact checked1497
theorem derived1497 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1497 := by
  apply localUnsat_implies_entails f1497 [c1459, c309, c327] c1497 unsat1497 (by rfl) a
  have h0 : Entails.eval a c1459 := derived1459 a h
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1498 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1498 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1494, some c1496, some c1497, some c1459, some c1476, some c564, some c253, some c1225, some c594, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1498 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1498 : lratChecker f1498 p1498 = .success := by decide +kernel
theorem unsat1498 : Unsatisfiable (PosFin 31) f1498 := by
  apply lratCheckerSound f1498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1498
  · intro a ha; simp [p1498] at ha; subst a; trivial
  · exact checked1498
theorem derived1498 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1498 := by
  apply localUnsat_implies_entails f1498 [c1441, c1494, c1496, c1497, c1459, c1476, c564, c253, c1225, c594] c1498 unsat1498 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1494 := derived1494 a h
  have h2 : Entails.eval a c1496 := derived1496 a h
  have h3 : Entails.eval a c1497 := derived1497 a h
  have h4 : Entails.eval a c1459 := derived1459 a h
  have h5 : Entails.eval a c1476 := derived1476 a h
  have h6 : Entails.eval a c564 := h 563 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c1225 := derived1225 a h
  have h9 : Entails.eval a c594 := h 593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1499 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1499 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1494, some c1459, some c1496, some c1497, some c1498, some c79, some c66, some c1240, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1499 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1499 : lratChecker f1499 p1499 = .success := by decide +kernel
theorem unsat1499 : Unsatisfiable (PosFin 31) f1499 := by
  apply lratCheckerSound f1499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1499
  · intro a ha; simp [p1499] at ha; subst a; trivial
  · exact checked1499
theorem derived1499 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1499 := by
  apply localUnsat_implies_entails f1499 [c1441, c1494, c1459, c1496, c1497, c1498, c79, c66, c1240] c1499 unsat1499 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1494 := derived1494 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c1496 := derived1496 a h
  have h4 : Entails.eval a c1497 := derived1497 a h
  have h5 : Entails.eval a c1498 := derived1498 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c1240 := derived1240 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1500 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1500 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c35, some c7, some c253, some c369, some c1253, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1500 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1500 : lratChecker f1500 p1500 = .success := by decide +kernel
theorem unsat1500 : Unsatisfiable (PosFin 31) f1500 := by
  apply lratCheckerSound f1500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1500
  · intro a ha; simp [p1500] at ha; subst a; trivial
  · exact checked1500
theorem derived1500 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1500 := by
  apply localUnsat_implies_entails f1500 [c1441, c35, c7, c253, c369, c1253] c1500 unsat1500 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1501 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1501 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1494, some c1459, some c1499, some c35, some c309, some c254, some c182, some c1500, some c1466, some c301, some c358, some c888, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1501 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1501 : lratChecker f1501 p1501 = .success := by decide +kernel
theorem unsat1501 : Unsatisfiable (PosFin 31) f1501 := by
  apply lratCheckerSound f1501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1501
  · intro a ha; simp [p1501] at ha; subst a; trivial
  · exact checked1501
theorem derived1501 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1501 := by
  apply localUnsat_implies_entails f1501 [c1494, c1459, c1499, c35, c309, c254, c182, c1500, c1466, c301, c358, c888] c1501 unsat1501 (by rfl) a
  have h0 : Entails.eval a c1494 := derived1494 a h
  have h1 : Entails.eval a c1459 := derived1459 a h
  have h2 : Entails.eval a c1499 := derived1499 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c1500 := derived1500 a h
  have h8 : Entails.eval a c1466 := derived1466 a h
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c888 := h 887 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1502 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1502 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1476, some c1494, some c1459, some c1501, some c52, some c33, some c35, some c66, some c48, some c1254, some c157, some c509, some c564, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1502 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1502 : lratChecker f1502 p1502 = .success := by decide +kernel
theorem unsat1502 : Unsatisfiable (PosFin 31) f1502 := by
  apply lratCheckerSound f1502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1502
  · intro a ha; simp [p1502] at ha; subst a; trivial
  · exact checked1502
theorem derived1502 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1502 := by
  apply localUnsat_implies_entails f1502 [c1441, c1476, c1494, c1459, c1501, c52, c33, c35, c66, c48, c1254, c157, c509, c564] c1502 unsat1502 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1476 := derived1476 a h
  have h2 : Entails.eval a c1494 := derived1494 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c1501 := derived1501 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c1254 := derived1254 a h
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c509 := h 508 (by decide)
  have h13 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1503 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c66, some c69, some c1207, some c1304, some c1450, some c757, some c1206, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1503 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 31) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1441, c66, c69, c1207, c1304, c1450, c757, c1206] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c1207 := derived1207 a h
  have h4 : Entails.eval a c1304 := derived1304 a h
  have h5 : Entails.eval a c1450 := derived1450 a h
  have h6 : Entails.eval a c757 := h 756 (by decide)
  have h7 : Entails.eval a c1206 := derived1206 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1503, some c1255, some c324, some c33, some c161, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1504 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 31) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1441, c1503, c1255, c324, c33, c161] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1503 := derived1503 a h
  have h2 : Entails.eval a c1255 := derived1255 a h
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c66, some c69, some c1207, some c1304, some c1450, some c120, some c1206, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1505 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 31) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c1441, c66, c69, c1207, c1304, c1450, c120, c1206] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c1207 := derived1207 a h
  have h4 : Entails.eval a c1304 := derived1304 a h
  have h5 : Entails.eval a c1450 := derived1450 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c1206 := derived1206 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1504, some c1505, some c1255, some c324, some c317, some c1240, some c709, some c581, some c249, some c154, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1506 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 31) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c1441, c1502, c1504, c1505, c1255, c324, c317, c1240, c709, c581, c249, c154] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1504 := derived1504 a h
  have h3 : Entails.eval a c1505 := derived1505 a h
  have h4 : Entails.eval a c1255 := derived1255 a h
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c1240 := derived1240 a h
  have h8 : Entails.eval a c709 := h 708 (by decide)
  have h9 : Entails.eval a c581 := h 580 (by decide)
  have h10 : Entails.eval a c249 := h 248 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨1, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1255, some c496, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1507 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 31) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1441, c1255, c496] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1255 := derived1255 a h
  have h2 : Entails.eval a c496 := h 495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1506, some c1507, some c66, some c69, some c1207, some c1306, some c671, some c1, some c394, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1508 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 31) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1441, c1502, c1506, c1507, c66, c69, c1207, c1306, c671, c1, c394] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1506 := derived1506 a h
  have h3 : Entails.eval a c1507 := derived1507 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c1207 := derived1207 a h
  have h7 : Entails.eval a c1306 := derived1306 a h
  have h8 : Entails.eval a c671 := h 670 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c394 := h 393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1508, some c35, some c1502, some c36, some c314, some c259, some c1507, some c2, some c248, some c389, some c1253, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1509 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 31) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1508, c35, c1502, c36, c314, c259, c1507, c2, c248, c389, c1253] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1508 := derived1508 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c1507 := derived1507 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1509, some c1508, some c35, some c1502, some c36, some c314, some c357, some c1304, some c300, some c1258, some c1252, some c1268, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1510 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 31) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c1509, c1508, c35, c1502, c36, c314, c357, c1304, c300, c1258, c1252, c1268] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c1509 := derived1509 a h
  have h1 : Entails.eval a c1508 := derived1508 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c1502 := derived1502 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c1304 := derived1304 a h
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c1258 := derived1258 a h
  have h10 : Entails.eval a c1252 := derived1252 a h
  have h11 : Entails.eval a c1268 := derived1268 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1502, some c1508, some c35, some c36, some c314, some c1509, some c1510, some c1255, some c324, some c317, some c1280, some c249, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1511 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 31) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c1502, c1508, c35, c36, c314, c1509, c1510, c1255, c324, c317, c1280, c249] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c1502 := derived1502 a h
  have h1 : Entails.eval a c1508 := derived1508 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c1509 := derived1509 a h
  have h6 : Entails.eval a c1510 := derived1510 a h
  have h7 : Entails.eval a c1255 := derived1255 a h
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c1280 := derived1280 a h
  have h11 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, true), (⟨26, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c705, some c79, some c518, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1512 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 31) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c1441, c705, c79, c518] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c705 := h 704 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c518 := h 517 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1293, some c1512, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1513 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 31) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c1293, c1512] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c1293 := derived1293 a h
  have h1 : Entails.eval a c1512 := derived1512 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1514 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c36, some c303, some c193, some c129, some c1513, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1514 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 31) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c36, c303, c193, c129, c1513] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c1513 := derived1513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c15, some c1294, some c616, some c1304, some c1007, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1515 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 31) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c1441, c15, c1294, c616, c1304, c1007] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c616 := h 615 (by decide)
  have h4 : Entails.eval a c1304 := derived1304 a h
  have h5 : Entails.eval a c1007 := derived1007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1221, some c1058, some c388, some c530, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1516 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 31) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c1441, c1221, c1058, c388, c530] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c1058 := derived1058 a h
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c530 := h 529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1516

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
