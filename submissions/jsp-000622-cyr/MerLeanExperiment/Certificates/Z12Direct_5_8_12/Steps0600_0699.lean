import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0500_0599

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1517 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c388, some c530, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1517 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 31) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1441, c388, c530] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c530 := h 529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1511, some c1514, some c1516, some c1515, some c303, some c319, some c1517, some c248, some c671, some c577, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1518 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 31) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c1441, c1502, c1511, c1514, c1516, c1515, c303, c319, c1517, c248, c671, c577] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1511 := derived1511 a h
  have h3 : Entails.eval a c1514 := derived1514 a h
  have h4 : Entails.eval a c1516 := derived1516 a h
  have h5 : Entails.eval a c1515 := derived1515 a h
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c1517 := derived1517 a h
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c671 := h 670 (by decide)
  have h11 : Entails.eval a c577 := h 576 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1502, some c291, some c283, some c1326, some c305, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1519 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 31) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c1502, c291, c283, c1326, c305] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c1502 := derived1502 a h
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c1326 := derived1326 a h
  have h4 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1221, some c1518, some c1519, some c1225, some c90, some c66, some c186, some c572, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1520 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 31) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c1441, c1502, c1221, c1518, c1519, c1225, c90, c66, c186, c572] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1518 := derived1518 a h
  have h4 : Entails.eval a c1519 := derived1519 a h
  have h5 : Entails.eval a c1225 := derived1225 a h
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c572 := h 571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1521 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, false), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1521 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1518, some c28, some c9, some c1492, some c1474, some c1450, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1521 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1521 : lratChecker f1521 p1521 = .success := by decide +kernel
theorem unsat1521 : Unsatisfiable (PosFin 31) f1521 := by
  apply lratCheckerSound f1521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1521
  · intro a ha; simp [p1521] at ha; subst a; trivial
  · exact checked1521
theorem derived1521 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1521 := by
  apply localUnsat_implies_entails f1521 [c1518, c28, c9, c1492, c1474, c1450] c1521 unsat1521 (by rfl) a
  have h0 : Entails.eval a c1518 := derived1518 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1492 := derived1492 a h
  have h4 : Entails.eval a c1474 := derived1474 a h
  have h5 : Entails.eval a c1450 := derived1450 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1522 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1522 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1518, some c1502, some c1520, some c388, some c722, some c1450, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1522 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1522 : lratChecker f1522 p1522 = .success := by decide +kernel
theorem unsat1522 : Unsatisfiable (PosFin 31) f1522 := by
  apply lratCheckerSound f1522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1522
  · intro a ha; simp [p1522] at ha; subst a; trivial
  · exact checked1522
theorem derived1522 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1522 := by
  apply localUnsat_implies_entails f1522 [c1441, c1518, c1502, c1520, c388, c722, c1450] c1522 unsat1522 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1518 := derived1518 a h
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c1520 := derived1520 a h
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c722 := h 721 (by decide)
  have h6 : Entails.eval a c1450 := derived1450 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1523 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1523 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c28, some c1450, some c561, some c298, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1523 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1523 : lratChecker f1523 p1523 = .success := by decide +kernel
theorem unsat1523 : Unsatisfiable (PosFin 31) f1523 := by
  apply lratCheckerSound f1523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1523
  · intro a ha; simp [p1523] at ha; subst a; trivial
  · exact checked1523
theorem derived1523 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1523 := by
  apply localUnsat_implies_entails f1523 [c1441, c28, c1450, c561, c298] c1523 unsat1523 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c561 := h 560 (by decide)
  have h4 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1524 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1524 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1522, some c1521, some c1502, some c319, some c28, some c1518, some c1523, some c1207, some c1492, some c79, some c220, some c466, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1524 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1524 : lratChecker f1524 p1524 = .success := by decide +kernel
theorem unsat1524 : Unsatisfiable (PosFin 31) f1524 := by
  apply lratCheckerSound f1524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1524
  · intro a ha; simp [p1524] at ha; subst a; trivial
  · exact checked1524
theorem derived1524 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1524 := by
  apply localUnsat_implies_entails f1524 [c1441, c1522, c1521, c1502, c319, c28, c1518, c1523, c1207, c1492, c79, c220, c466] c1524 unsat1524 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1522 := derived1522 a h
  have h2 : Entails.eval a c1521 := derived1521 a h
  have h3 : Entails.eval a c1502 := derived1502 a h
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1518 := derived1518 a h
  have h7 : Entails.eval a c1523 := derived1523 a h
  have h8 : Entails.eval a c1207 := derived1207 a h
  have h9 : Entails.eval a c1492 := derived1492 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c466 := h 465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1525 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1525 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1524, some c1221, some c1522, some c28, some c1518, some c1207, some c323, some c1492, some c1495, some c1297, some c599, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1525 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1525 : lratChecker f1525 p1525 = .success := by decide +kernel
theorem unsat1525 : Unsatisfiable (PosFin 31) f1525 := by
  apply lratCheckerSound f1525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1525
  · intro a ha; simp [p1525] at ha; subst a; trivial
  · exact checked1525
theorem derived1525 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1525 := by
  apply localUnsat_implies_entails f1525 [c1441, c1502, c1524, c1221, c1522, c28, c1518, c1207, c323, c1492, c1495, c1297, c599] c1525 unsat1525 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1524 := derived1524 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1522 := derived1522 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1518 := derived1518 a h
  have h7 : Entails.eval a c1207 := derived1207 a h
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c1492 := derived1492 a h
  have h10 : Entails.eval a c1495 := derived1495 a h
  have h11 : Entails.eval a c1297 := derived1297 a h
  have h12 : Entails.eval a c599 := h 598 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1526 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1526 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1518, some c1502, some c1522, some c28, some c1521, some c1525, some c1450, some c355, some c322, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1526 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1526 : lratChecker f1526 p1526 = .success := by decide +kernel
theorem unsat1526 : Unsatisfiable (PosFin 31) f1526 := by
  apply lratCheckerSound f1526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1526
  · intro a ha; simp [p1526] at ha; subst a; trivial
  · exact checked1526
theorem derived1526 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1526 := by
  apply localUnsat_implies_entails f1526 [c1518, c1502, c1522, c28, c1521, c1525, c1450, c355, c322] c1526 unsat1526 (by rfl) a
  have h0 : Entails.eval a c1518 := derived1518 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1522 := derived1522 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1521 := derived1521 a h
  have h5 : Entails.eval a c1525 := derived1525 a h
  have h6 : Entails.eval a c1450 := derived1450 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1527 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1527 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1450, some c1206, some c265, some c135, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1527 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1527 : lratChecker f1527 p1527 = .success := by decide +kernel
theorem unsat1527 : Unsatisfiable (PosFin 31) f1527 := by
  apply lratCheckerSound f1527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1527
  · intro a ha; simp [p1527] at ha; subst a; trivial
  · exact checked1527
theorem derived1527 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1527 := by
  apply localUnsat_implies_entails f1527 [c1441, c1450, c1206, c265, c135] c1527 unsat1527 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1450 := derived1450 a h
  have h2 : Entails.eval a c1206 := derived1206 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1528 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1528 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1518, some c1502, some c1526, some c1505, some c1515, some c1221, some c1527, some c1207, some c79, some c1240, some c1226, some c513, some c388, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1528 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1528 : lratChecker f1528 p1528 = .success := by decide +kernel
theorem unsat1528 : Unsatisfiable (PosFin 31) f1528 := by
  apply lratCheckerSound f1528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1528
  · intro a ha; simp [p1528] at ha; subst a; trivial
  · exact checked1528
theorem derived1528 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1528 := by
  apply localUnsat_implies_entails f1528 [c1441, c1518, c1502, c1526, c1505, c1515, c1221, c1527, c1207, c79, c1240, c1226, c513, c388] c1528 unsat1528 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1518 := derived1518 a h
  have h2 : Entails.eval a c1502 := derived1502 a h
  have h3 : Entails.eval a c1526 := derived1526 a h
  have h4 : Entails.eval a c1505 := derived1505 a h
  have h5 : Entails.eval a c1515 := derived1515 a h
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c1527 := derived1527 a h
  have h8 : Entails.eval a c1207 := derived1207 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c1240 := derived1240 a h
  have h11 : Entails.eval a c1226 := derived1226 a h
  have h12 : Entails.eval a c513 := h 512 (by decide)
  have h13 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1529 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1529 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1502, some c1518, some c1528, some c31, some c36, some c68, some c35, some c306, some c1022, some c103, some c59, some c1253, some c74, some c389, some c57, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1529 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1529 : lratChecker f1529 p1529 = .success := by decide +kernel
theorem unsat1529 : Unsatisfiable (PosFin 31) f1529 := by
  apply lratCheckerSound f1529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1529
  · intro a ha; simp [p1529] at ha; subst a; trivial
  · exact checked1529
theorem derived1529 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1529 := by
  apply localUnsat_implies_entails f1529 [c1441, c1502, c1518, c1528, c31, c36, c68, c35, c306, c1022, c103, c59, c1253, c74, c389, c57] c1529 unsat1529 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1502 := derived1502 a h
  have h2 : Entails.eval a c1518 := derived1518 a h
  have h3 : Entails.eval a c1528 := derived1528 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c1022 := derived1022 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c1253 := derived1253 a h
  have h13 : Entails.eval a c74 := h 73 (by decide)
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1530 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1530 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1264, some c17, some c1140, some c189, some c1206, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1530 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1530 : lratChecker f1530 p1530 = .success := by decide +kernel
theorem unsat1530 : Unsatisfiable (PosFin 31) f1530 := by
  apply lratCheckerSound f1530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1530
  · intro a ha; simp [p1530] at ha; subst a; trivial
  · exact checked1530
theorem derived1530 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1530 := by
  apply localUnsat_implies_entails f1530 [c1441, c1529, c1264, c17, c1140, c189, c1206] c1530 unsat1530 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1264 := derived1264 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c1206 := derived1206 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1531 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1531 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1530, some c1529, some c1140, some c1206, some c265, some c79, some c189, some c28, some c1204, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1531 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1531 : lratChecker f1531 p1531 = .success := by decide +kernel
theorem unsat1531 : Unsatisfiable (PosFin 31) f1531 := by
  apply lratCheckerSound f1531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1531
  · intro a ha; simp [p1531] at ha; subst a; trivial
  · exact checked1531
theorem derived1531 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1531 := by
  apply localUnsat_implies_entails f1531 [c1441, c1530, c1529, c1140, c1206, c265, c79, c189, c28, c1204] c1531 unsat1531 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1530 := derived1530 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c1206 := derived1206 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c1204 := derived1204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1532 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1532 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1530, some c1531, some c82, some c1282, some c1206, some c1325, some c1203, some c270, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1532 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1532 : lratChecker f1532 p1532 = .success := by decide +kernel
theorem unsat1532 : Unsatisfiable (PosFin 31) f1532 := by
  apply lratCheckerSound f1532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1532
  · intro a ha; simp [p1532] at ha; subst a; trivial
  · exact checked1532
theorem derived1532 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1532 := by
  apply localUnsat_implies_entails f1532 [c1441, c1529, c1530, c1531, c82, c1282, c1206, c1325, c1203, c270] c1532 unsat1532 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1530 := derived1530 a h
  have h3 : Entails.eval a c1531 := derived1531 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1206 := derived1206 a h
  have h7 : Entails.eval a c1325 := derived1325 a h
  have h8 : Entails.eval a c1203 := derived1203 a h
  have h9 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1533 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1533 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c166, some c1207, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1533 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1533 : lratChecker f1533 p1533 = .success := by decide +kernel
theorem unsat1533 : Unsatisfiable (PosFin 31) f1533 := by
  apply lratCheckerSound f1533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1533
  · intro a ha; simp [p1533] at ha; subst a; trivial
  · exact checked1533
theorem derived1533 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1533 := by
  apply localUnsat_implies_entails f1533 [c53, c166, c1207] c1533 unsat1533 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c1207 := derived1207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1534 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1534 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1533, some c1206, some c79, some c135, some c1207, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1534 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1534 : lratChecker f1534 p1534 = .success := by decide +kernel
theorem unsat1534 : Unsatisfiable (PosFin 31) f1534 := by
  apply lratCheckerSound f1534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1534
  · intro a ha; simp [p1534] at ha; subst a; trivial
  · exact checked1534
theorem derived1534 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1534 := by
  apply localUnsat_implies_entails f1534 [c1441, c1533, c1206, c79, c135, c1207] c1534 unsat1534 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1533 := derived1533 a h
  have h2 : Entails.eval a c1206 := derived1206 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c1207 := derived1207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1535 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1535 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1534, some c79, some c82, some c189, some c1207, some c1252, some c1204, some c176, some c1274, some c297, some c1283, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1535 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1535 : lratChecker f1535 p1535 = .success := by decide +kernel
theorem unsat1535 : Unsatisfiable (PosFin 31) f1535 := by
  apply lratCheckerSound f1535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1535
  · intro a ha; simp [p1535] at ha; subst a; trivial
  · exact checked1535
theorem derived1535 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1535 := by
  apply localUnsat_implies_entails f1535 [c1441, c1534, c79, c82, c189, c1207, c1252, c1204, c176, c1274, c297, c1283] c1535 unsat1535 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1534 := derived1534 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c1207 := derived1207 a h
  have h6 : Entails.eval a c1252 := derived1252 a h
  have h7 : Entails.eval a c1204 := derived1204 a h
  have h8 : Entails.eval a c176 := h 175 (by decide)
  have h9 : Entails.eval a c1274 := derived1274 a h
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c1283 := derived1283 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1536 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1536 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1529, some c1534, some c1532, some c1221, some c1535, some c1206, some c53, some c1140, some c256, some c34, some c1314, some c318, some c1237, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1536 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1536 : lratChecker f1536 p1536 = .success := by decide +kernel
theorem unsat1536 : Unsatisfiable (PosFin 31) f1536 := by
  apply lratCheckerSound f1536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1536
  · intro a ha; simp [p1536] at ha; subst a; trivial
  · exact checked1536
theorem derived1536 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1536 := by
  apply localUnsat_implies_entails f1536 [c1529, c1534, c1532, c1221, c1535, c1206, c53, c1140, c256, c34, c1314, c318, c1237] c1536 unsat1536 (by rfl) a
  have h0 : Entails.eval a c1529 := derived1529 a h
  have h1 : Entails.eval a c1534 := derived1534 a h
  have h2 : Entails.eval a c1532 := derived1532 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1535 := derived1535 a h
  have h5 : Entails.eval a c1206 := derived1206 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c1140 := derived1140 a h
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c1314 := derived1314 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c1237 := derived1237 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1537 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1537 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1240, some c1237, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1537 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1537 : lratChecker f1537 p1537 = .success := by decide +kernel
theorem unsat1537 : Unsatisfiable (PosFin 31) f1537 := by
  apply lratCheckerSound f1537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1537
  · intro a ha; simp [p1537] at ha; subst a; trivial
  · exact checked1537
theorem derived1537 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1537 := by
  apply localUnsat_implies_entails f1537 [c1240, c1237] c1537 unsat1537 (by rfl) a
  have h0 : Entails.eval a c1240 := derived1240 a h
  have h1 : Entails.eval a c1237 := derived1237 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1538 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1538 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1529, some c1296, some c272, some c816, some c643, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1538 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1538 : lratChecker f1538 p1538 = .success := by decide +kernel
theorem unsat1538 : Unsatisfiable (PosFin 31) f1538 := by
  apply lratCheckerSound f1538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1538
  · intro a ha; simp [p1538] at ha; subst a; trivial
  · exact checked1538
theorem derived1538 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1538 := by
  apply localUnsat_implies_entails f1538 [c1536, c1529, c1296, c272, c816, c643] c1538 unsat1538 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1296 := derived1296 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c816 := h 815 (by decide)
  have h5 : Entails.eval a c643 := h 642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1539 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1539 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c1307, some c157, some c565, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1539 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1539 : lratChecker f1539 p1539 = .success := by decide +kernel
theorem unsat1539 : Unsatisfiable (PosFin 31) f1539 := by
  apply lratCheckerSound f1539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1539
  · intro a ha; simp [p1539] at ha; subst a; trivial
  · exact checked1539
theorem derived1539 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1539 := by
  apply localUnsat_implies_entails f1539 [c52, c1307, c157, c565] c1539 unsat1539 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c1307 := derived1307 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c565 := h 564 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1540 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1540 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1537, some c1538, some c1459, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1540 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1540 : lratChecker f1540 p1540 = .success := by decide +kernel
theorem unsat1540 : Unsatisfiable (PosFin 31) f1540 := by
  apply lratCheckerSound f1540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1540
  · intro a ha; simp [p1540] at ha; subst a; trivial
  · exact checked1540
theorem derived1540 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1540 := by
  apply localUnsat_implies_entails f1540 [c1536, c1537, c1538, c1459] c1540 unsat1540 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1537 := derived1537 a h
  have h2 : Entails.eval a c1538 := derived1538 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1541 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1541 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1529, some c1539, some c1540, some c256, some c1317, some c1323, some c1459, some c1497, some c1240, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1541 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1541 : lratChecker f1541 p1541 = .success := by decide +kernel
theorem unsat1541 : Unsatisfiable (PosFin 31) f1541 := by
  apply lratCheckerSound f1541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1541
  · intro a ha; simp [p1541] at ha; subst a; trivial
  · exact checked1541
theorem derived1541 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1541 := by
  apply localUnsat_implies_entails f1541 [c1536, c1529, c1539, c1540, c256, c1317, c1323, c1459, c1497, c1240] c1541 unsat1541 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1539 := derived1539 a h
  have h3 : Entails.eval a c1540 := derived1540 a h
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c1317 := derived1317 a h
  have h6 : Entails.eval a c1323 := derived1323 a h
  have h7 : Entails.eval a c1459 := derived1459 a h
  have h8 : Entails.eval a c1497 := derived1497 a h
  have h9 : Entails.eval a c1240 := derived1240 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1542 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1542 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c45, some c1317, some c86, some c61, some c806, some c823, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1542 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1542 : lratChecker f1542 p1542 = .success := by decide +kernel
theorem unsat1542 : Unsatisfiable (PosFin 31) f1542 := by
  apply lratCheckerSound f1542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1542
  · intro a ha; simp [p1542] at ha; subst a; trivial
  · exact checked1542
theorem derived1542 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1542 := by
  apply localUnsat_implies_entails f1542 [c45, c1317, c86, c61, c806, c823] c1542 unsat1542 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c1317 := derived1317 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c806 := h 805 (by decide)
  have h5 : Entails.eval a c823 := h 822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1543 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1543 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1542, some c52, some c157, some c1273, some c526, some c1459, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1543 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1543 : lratChecker f1543 p1543 = .success := by decide +kernel
theorem unsat1543 : Unsatisfiable (PosFin 31) f1543 := by
  apply lratCheckerSound f1543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1543
  · intro a ha; simp [p1543] at ha; subst a; trivial
  · exact checked1543
theorem derived1543 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1543 := by
  apply localUnsat_implies_entails f1543 [c1542, c52, c157, c1273, c526, c1459] c1543 unsat1543 (by rfl) a
  have h0 : Entails.eval a c1542 := derived1542 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c1273 := derived1273 a h
  have h4 : Entails.eval a c526 := h 525 (by decide)
  have h5 : Entails.eval a c1459 := derived1459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1544 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1544 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1536, some c1529, some c1541, some c1140, some c1543, some c1267, some c865, some c438, some c1231, some c272, some c1203, some c465, some c378, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1544 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1544 : lratChecker f1544 p1544 = .success := by decide +kernel
theorem unsat1544 : Unsatisfiable (PosFin 31) f1544 := by
  apply lratCheckerSound f1544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1544
  · intro a ha; simp [p1544] at ha; subst a; trivial
  · exact checked1544
theorem derived1544 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1544 := by
  apply localUnsat_implies_entails f1544 [c1441, c1536, c1529, c1541, c1140, c1543, c1267, c865, c438, c1231, c272, c1203, c465, c378] c1544 unsat1544 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1541 := derived1541 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c1543 := derived1543 a h
  have h6 : Entails.eval a c1267 := derived1267 a h
  have h7 : Entails.eval a c865 := h 864 (by decide)
  have h8 : Entails.eval a c438 := h 437 (by decide)
  have h9 : Entails.eval a c1231 := derived1231 a h
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c1203 := derived1203 a h
  have h12 : Entails.eval a c465 := h 464 (by decide)
  have h13 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1545 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1545 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1529, some c1214, some c1459, some c59, some c57, some c1288, some c1140, some c758, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1545 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1545 : lratChecker f1545 p1545 = .success := by decide +kernel
theorem unsat1545 : Unsatisfiable (PosFin 31) f1545 := by
  apply lratCheckerSound f1545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1545
  · intro a ha; simp [p1545] at ha; subst a; trivial
  · exact checked1545
theorem derived1545 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1545 := by
  apply localUnsat_implies_entails f1545 [c1536, c1529, c1214, c1459, c59, c57, c1288, c1140, c758] c1545 unsat1545 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1214 := derived1214 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c1288 := derived1288 a h
  have h7 : Entails.eval a c1140 := derived1140 a h
  have h8 : Entails.eval a c758 := h 757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1546 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1546 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1529, some c1545, some c1541, some c1544, some c1140, some c1232, some c1543, some c1309, some c8, some c1459, some c706, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1546 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1546 : lratChecker f1546 p1546 = .success := by decide +kernel
theorem unsat1546 : Unsatisfiable (PosFin 31) f1546 := by
  apply lratCheckerSound f1546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1546
  · intro a ha; simp [p1546] at ha; subst a; trivial
  · exact checked1546
theorem derived1546 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1546 := by
  apply localUnsat_implies_entails f1546 [c1536, c1529, c1545, c1541, c1544, c1140, c1232, c1543, c1309, c8, c1459, c706] c1546 unsat1546 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1545 := derived1545 a h
  have h3 : Entails.eval a c1541 := derived1541 a h
  have h4 : Entails.eval a c1544 := derived1544 a h
  have h5 : Entails.eval a c1140 := derived1140 a h
  have h6 : Entails.eval a c1232 := derived1232 a h
  have h7 : Entails.eval a c1543 := derived1543 a h
  have h8 : Entails.eval a c1309 := derived1309 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c1459 := derived1459 a h
  have h11 : Entails.eval a c706 := h 705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1547 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1547 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c189, some c79, some c1204, some c591, some c1459, some c781, some c1219, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1547 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1547 : lratChecker f1547 p1547 = .success := by decide +kernel
theorem unsat1547 : Unsatisfiable (PosFin 31) f1547 := by
  apply lratCheckerSound f1547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1547
  · intro a ha; simp [p1547] at ha; subst a; trivial
  · exact checked1547
theorem derived1547 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1547 := by
  apply localUnsat_implies_entails f1547 [c1441, c189, c79, c1204, c591, c1459, c781, c1219] c1547 unsat1547 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c591 := h 590 (by decide)
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c781 := h 780 (by decide)
  have h7 : Entails.eval a c1219 := derived1219 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1548 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1548 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1536, some c1529, some c1546, some c79, some c82, some c189, some c1204, some c1140, some c1547, some c1478, some c253, some c17, some c894, some c1223, some c1250, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1548 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1548 : lratChecker f1548 p1548 = .success := by decide +kernel
theorem unsat1548 : Unsatisfiable (PosFin 31) f1548 := by
  apply lratCheckerSound f1548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1548
  · intro a ha; simp [p1548] at ha; subst a; trivial
  · exact checked1548
theorem derived1548 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1548 := by
  apply localUnsat_implies_entails f1548 [c1441, c1536, c1529, c1546, c79, c82, c189, c1204, c1140, c1547, c1478, c253, c17, c894, c1223, c1250] c1548 unsat1548 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1546 := derived1546 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c1204 := derived1204 a h
  have h8 : Entails.eval a c1140 := derived1140 a h
  have h9 : Entails.eval a c1547 := derived1547 a h
  have h10 : Entails.eval a c1478 := derived1478 a h
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c894 := h 893 (by decide)
  have h14 : Entails.eval a c1223 := derived1223 a h
  have h15 : Entails.eval a c1250 := derived1250 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1549 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1549 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c135, some c79, some c1547, some c189, some c184, some c1204, some c48, some c253, some c132, some c378, some c377, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1549 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1549 : lratChecker f1549 p1549 = .success := by decide +kernel
theorem unsat1549 : Unsatisfiable (PosFin 31) f1549 := by
  apply lratCheckerSound f1549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1549
  · intro a ha; simp [p1549] at ha; subst a; trivial
  · exact checked1549
theorem derived1549 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1549 := by
  apply localUnsat_implies_entails f1549 [c1441, c135, c79, c1547, c189, c184, c1204, c48, c253, c132, c378, c377] c1549 unsat1549 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c1547 := derived1547 a h
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c1204 := derived1204 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c253 := h 252 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1550 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1550 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1549, some c135, some c79, some c184, some c33, some c48, some c130, some c132, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1550 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1550 : lratChecker f1550 p1550 = .success := by decide +kernel
theorem unsat1550 : Unsatisfiable (PosFin 31) f1550 := by
  apply lratCheckerSound f1550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1550
  · intro a ha; simp [p1550] at ha; subst a; trivial
  · exact checked1550
theorem derived1550 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1550 := by
  apply localUnsat_implies_entails f1550 [c1441, c1549, c135, c79, c184, c33, c48, c130, c132] c1550 unsat1550 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1549 := derived1549 a h
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1551 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1551 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c79, some c33, some c48, some c1459, some c64, some c1210, some c1300, some c591, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1551 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1551 : lratChecker f1551 p1551 = .success := by decide +kernel
theorem unsat1551 : Unsatisfiable (PosFin 31) f1551 := by
  apply lratCheckerSound f1551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1551
  · intro a ha; simp [p1551] at ha; subst a; trivial
  · exact checked1551
theorem derived1551 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1551 := by
  apply localUnsat_implies_entails f1551 [c1441, c79, c33, c48, c1459, c64, c1210, c1300, c591] c1551 unsat1551 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c1459 := derived1459 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1300 := derived1300 a h
  have h8 : Entails.eval a c591 := h 590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1552 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1552 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1551, some c52, some c254, some c309, some c718, some c675, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1552 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1552 : lratChecker f1552 p1552 = .success := by decide +kernel
theorem unsat1552 : Unsatisfiable (PosFin 31) f1552 := by
  apply lratCheckerSound f1552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1552
  · intro a ha; simp [p1552] at ha; subst a; trivial
  · exact checked1552
theorem derived1552 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1552 := by
  apply localUnsat_implies_entails f1552 [c1441, c1551, c52, c254, c309, c718, c675] c1552 unsat1552 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1551 := derived1551 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c718 := h 717 (by decide)
  have h6 : Entails.eval a c675 := h 674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1553 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1553 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c52, some c254, some c268, some c44, some c309, some c628, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1553 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1553 : lratChecker f1553 p1553 = .success := by decide +kernel
theorem unsat1553 : Unsatisfiable (PosFin 31) f1553 := by
  apply lratCheckerSound f1553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1553
  · intro a ha; simp [p1553] at ha; subst a; trivial
  · exact checked1553
theorem derived1553 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1553 := by
  apply localUnsat_implies_entails f1553 [c1441, c52, c254, c268, c44, c309, c628] c1553 unsat1553 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c254 := h 253 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1554 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1554 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c79, some c135, some c1549, some c1550, some c1552, some c1553, some c33, some c48, some c1459, some c64, some c72, some c54, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1554 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1554 : lratChecker f1554 p1554 = .success := by decide +kernel
theorem unsat1554 : Unsatisfiable (PosFin 31) f1554 := by
  apply lratCheckerSound f1554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1554
  · intro a ha; simp [p1554] at ha; subst a; trivial
  · exact checked1554
theorem derived1554 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1554 := by
  apply localUnsat_implies_entails f1554 [c1441, c79, c135, c1549, c1550, c1552, c1553, c33, c48, c1459, c64, c72, c54] c1554 unsat1554 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c1549 := derived1549 a h
  have h4 : Entails.eval a c1550 := derived1550 a h
  have h5 : Entails.eval a c1552 := derived1552 a h
  have h6 : Entails.eval a c1553 := derived1553 a h
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c1459 := derived1459 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1555 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1555 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c1231, some c1459, some c931, some c891, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1555 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1555 : lratChecker f1555 p1555 = .success := by decide +kernel
theorem unsat1555 : Unsatisfiable (PosFin 31) f1555 := by
  apply lratCheckerSound f1555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1555
  · intro a ha; simp [p1555] at ha; subst a; trivial
  · exact checked1555
theorem derived1555 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1555 := by
  apply localUnsat_implies_entails f1555 [c33, c1231, c1459, c931, c891] c1555 unsat1555 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c891 := h 890 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1556 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1556 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1536, some c1548, some c1554, some c1314, some c1555, some c52, some c309, some c1296, some c74, some c559, some c573, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1556 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1556 : lratChecker f1556 p1556 = .success := by decide +kernel
theorem unsat1556 : Unsatisfiable (PosFin 31) f1556 := by
  apply lratCheckerSound f1556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1556
  · intro a ha; simp [p1556] at ha; subst a; trivial
  · exact checked1556
theorem derived1556 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1556 := by
  apply localUnsat_implies_entails f1556 [c1441, c1529, c1536, c1548, c1554, c1314, c1555, c52, c309, c1296, c74, c559, c573] c1556 unsat1556 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1536 := derived1536 a h
  have h3 : Entails.eval a c1548 := derived1548 a h
  have h4 : Entails.eval a c1554 := derived1554 a h
  have h5 : Entails.eval a c1314 := derived1314 a h
  have h6 : Entails.eval a c1555 := derived1555 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c1296 := derived1296 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c559 := h 558 (by decide)
  have h12 : Entails.eval a c573 := h 572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1557 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1557 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1529, some c1536, some c1548, some c1554, some c1556, some c53, some c43, some c55, some c1218, some c725, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1557 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1557 : lratChecker f1557 p1557 = .success := by decide +kernel
theorem unsat1557 : Unsatisfiable (PosFin 31) f1557 := by
  apply lratCheckerSound f1557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1557
  · intro a ha; simp [p1557] at ha; subst a; trivial
  · exact checked1557
theorem derived1557 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1557 := by
  apply localUnsat_implies_entails f1557 [c1529, c1536, c1548, c1554, c1556, c53, c43, c55, c1218, c725] c1557 unsat1557 (by rfl) a
  have h0 : Entails.eval a c1529 := derived1529 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c1548 := derived1548 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c1556 := derived1556 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c1218 := derived1218 a h
  have h9 : Entails.eval a c725 := h 724 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1558 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1558 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1220, some c53, some c1232, some c1270, some c721, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1558 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1558 : lratChecker f1558 p1558 = .success := by decide +kernel
theorem unsat1558 : Unsatisfiable (PosFin 31) f1558 := by
  apply lratCheckerSound f1558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1558
  · intro a ha; simp [p1558] at ha; subst a; trivial
  · exact checked1558
theorem derived1558 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1558 := by
  apply localUnsat_implies_entails f1558 [c1220, c53, c1232, c1270, c721] c1558 unsat1558 (by rfl) a
  have h0 : Entails.eval a c1220 := derived1220 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c1232 := derived1232 a h
  have h3 : Entails.eval a c1270 := derived1270 a h
  have h4 : Entails.eval a c721 := h 720 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1559 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1559 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1529, some c1548, some c1536, some c1554, some c1220, some c1459, some c1558, some c140, some c869, some c1296, some c290, some c52, some c39, some c1285, some c266, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1559 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1559 : lratChecker f1559 p1559 = .success := by decide +kernel
theorem unsat1559 : Unsatisfiable (PosFin 31) f1559 := by
  apply lratCheckerSound f1559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1559
  · intro a ha; simp [p1559] at ha; subst a; trivial
  · exact checked1559
theorem derived1559 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1559 := by
  apply localUnsat_implies_entails f1559 [c1529, c1548, c1536, c1554, c1220, c1459, c1558, c140, c869, c1296, c290, c52, c39, c1285, c266] c1559 unsat1559 (by rfl) a
  have h0 : Entails.eval a c1529 := derived1529 a h
  have h1 : Entails.eval a c1548 := derived1548 a h
  have h2 : Entails.eval a c1536 := derived1536 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c1220 := derived1220 a h
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c1558 := derived1558 a h
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c869 := h 868 (by decide)
  have h9 : Entails.eval a c1296 := derived1296 a h
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c1285 := derived1285 a h
  have h14 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1560 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1560 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1529, some c1536, some c1548, some c1554, some c1557, some c1220, some c1459, some c1558, some c1559, some c166, some c1229, some c1276, some c312, some c352, some c1489, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1560 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1560 : lratChecker f1560 p1560 = .success := by decide +kernel
theorem unsat1560 : Unsatisfiable (PosFin 31) f1560 := by
  apply lratCheckerSound f1560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1560
  · intro a ha; simp [p1560] at ha; subst a; trivial
  · exact checked1560
theorem derived1560 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1560 := by
  apply localUnsat_implies_entails f1560 [c1529, c1536, c1548, c1554, c1557, c1220, c1459, c1558, c1559, c166, c1229, c1276, c312, c352, c1489] c1560 unsat1560 (by rfl) a
  have h0 : Entails.eval a c1529 := derived1529 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c1548 := derived1548 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c1557 := derived1557 a h
  have h5 : Entails.eval a c1220 := derived1220 a h
  have h6 : Entails.eval a c1459 := derived1459 a h
  have h7 : Entails.eval a c1558 := derived1558 a h
  have h8 : Entails.eval a c1559 := derived1559 a h
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c1229 := derived1229 a h
  have h11 : Entails.eval a c1276 := derived1276 a h
  have h12 : Entails.eval a c312 := h 311 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c1489 := derived1489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1561 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1561 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1560, some c1529, some c1536, some c1548, some c1554, some c1220, some c1559, some c1459, some c311, some c166, some c1204, some c1244, some c1478, some c352, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1561 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1561 : lratChecker f1561 p1561 = .success := by decide +kernel
theorem unsat1561 : Unsatisfiable (PosFin 31) f1561 := by
  apply lratCheckerSound f1561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1561
  · intro a ha; simp [p1561] at ha; subst a; trivial
  · exact checked1561
theorem derived1561 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1561 := by
  apply localUnsat_implies_entails f1561 [c1560, c1529, c1536, c1548, c1554, c1220, c1559, c1459, c311, c166, c1204, c1244, c1478, c352] c1561 unsat1561 (by rfl) a
  have h0 : Entails.eval a c1560 := derived1560 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1536 := derived1536 a h
  have h3 : Entails.eval a c1548 := derived1548 a h
  have h4 : Entails.eval a c1554 := derived1554 a h
  have h5 : Entails.eval a c1220 := derived1220 a h
  have h6 : Entails.eval a c1559 := derived1559 a h
  have h7 : Entails.eval a c1459 := derived1459 a h
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c1204 := derived1204 a h
  have h11 : Entails.eval a c1244 := derived1244 a h
  have h12 : Entails.eval a c1478 := derived1478 a h
  have h13 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1562 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1562 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c55, some c107, some c595, some c1300, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1562 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1562 : lratChecker f1562 p1562 = .success := by decide +kernel
theorem unsat1562 : Unsatisfiable (PosFin 31) f1562 := by
  apply lratCheckerSound f1562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1562
  · intro a ha; simp [p1562] at ha; subst a; trivial
  · exact checked1562
theorem derived1562 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1562 := by
  apply localUnsat_implies_entails f1562 [c1441, c55, c107, c595, c1300] c1562 unsat1562 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c595 := h 594 (by decide)
  have h4 : Entails.eval a c1300 := derived1300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1563 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1563 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1536, some c1529, some c1560, some c1561, some c1562, some c1459, some c1548, some c1554, some c1203, some c1259, some c931, some c1231, some c15, some c309, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1563 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1563 : lratChecker f1563 p1563 = .success := by decide +kernel
theorem unsat1563 : Unsatisfiable (PosFin 31) f1563 := by
  apply lratCheckerSound f1563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1563
  · intro a ha; simp [p1563] at ha; subst a; trivial
  · exact checked1563
theorem derived1563 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1563 := by
  apply localUnsat_implies_entails f1563 [c1536, c1529, c1560, c1561, c1562, c1459, c1548, c1554, c1203, c1259, c931, c1231, c15, c309] c1563 unsat1563 (by rfl) a
  have h0 : Entails.eval a c1536 := derived1536 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1560 := derived1560 a h
  have h3 : Entails.eval a c1561 := derived1561 a h
  have h4 : Entails.eval a c1562 := derived1562 a h
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c1548 := derived1548 a h
  have h7 : Entails.eval a c1554 := derived1554 a h
  have h8 : Entails.eval a c1203 := derived1203 a h
  have h9 : Entails.eval a c1259 := derived1259 a h
  have h10 : Entails.eval a c931 := derived931 a h
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1564 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1564 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1529, some c1536, some c1548, some c1554, some c1560, some c1561, some c1562, some c1459, some c1247, some c1563, some c1497, some c354, some c706, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1564 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1564 : lratChecker f1564 p1564 = .success := by decide +kernel
theorem unsat1564 : Unsatisfiable (PosFin 31) f1564 := by
  apply lratCheckerSound f1564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1564
  · intro a ha; simp [p1564] at ha; subst a; trivial
  · exact checked1564
theorem derived1564 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1564 := by
  apply localUnsat_implies_entails f1564 [c1529, c1536, c1548, c1554, c1560, c1561, c1562, c1459, c1247, c1563, c1497, c354, c706] c1564 unsat1564 (by rfl) a
  have h0 : Entails.eval a c1529 := derived1529 a h
  have h1 : Entails.eval a c1536 := derived1536 a h
  have h2 : Entails.eval a c1548 := derived1548 a h
  have h3 : Entails.eval a c1554 := derived1554 a h
  have h4 : Entails.eval a c1560 := derived1560 a h
  have h5 : Entails.eval a c1561 := derived1561 a h
  have h6 : Entails.eval a c1562 := derived1562 a h
  have h7 : Entails.eval a c1459 := derived1459 a h
  have h8 : Entails.eval a c1247 := derived1247 a h
  have h9 : Entails.eval a c1563 := derived1563 a h
  have h10 : Entails.eval a c1497 := derived1497 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c706 := h 705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1565 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1565 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1459, some c1564, some c594, some c1497, some c254, some c15, some c593, some c729, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1565 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1565 : lratChecker f1565 p1565 = .success := by decide +kernel
theorem unsat1565 : Unsatisfiable (PosFin 31) f1565 := by
  apply lratCheckerSound f1565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1565
  · intro a ha; simp [p1565] at ha; subst a; trivial
  · exact checked1565
theorem derived1565 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1565 := by
  apply localUnsat_implies_entails f1565 [c1441, c1459, c1564, c594, c1497, c254, c15, c593, c729] c1565 unsat1565 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1459 := derived1459 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c594 := h 593 (by decide)
  have h4 : Entails.eval a c1497 := derived1497 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c593 := h 592 (by decide)
  have h8 : Entails.eval a c729 := h 728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1566 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1566 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1564, some c254, some c15, some c412, some c748, some c216, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1566 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1566 : lratChecker f1566 p1566 = .success := by decide +kernel
theorem unsat1566 : Unsatisfiable (PosFin 31) f1566 := by
  apply lratCheckerSound f1566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1566
  · intro a ha; simp [p1566] at ha; subst a; trivial
  · exact checked1566
theorem derived1566 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1566 := by
  apply localUnsat_implies_entails f1566 [c1441, c1564, c254, c15, c412, c748, c216] c1566 unsat1566 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c254 := h 253 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c412 := h 411 (by decide)
  have h5 : Entails.eval a c748 := h 747 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1567 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1567 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c412, some c554, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1567 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1567 : lratChecker f1567 p1567 = .success := by decide +kernel
theorem unsat1567 : Unsatisfiable (PosFin 31) f1567 := by
  apply lratCheckerSound f1567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1567
  · intro a ha; simp [p1567] at ha; subst a; trivial
  · exact checked1567
theorem derived1567 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1567 := by
  apply localUnsat_implies_entails f1567 [c1441, c412, c554] c1567 unsat1567 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c412 := h 411 (by decide)
  have h2 : Entails.eval a c554 := h 553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1568 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1568 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1564, some c1459, some c1565, some c1566, some c309, some c1567, some c1254, some c79, some c66, some c1218, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1568 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1568 : lratChecker f1568 p1568 = .success := by decide +kernel
theorem unsat1568 : Unsatisfiable (PosFin 31) f1568 := by
  apply lratCheckerSound f1568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1568
  · intro a ha; simp [p1568] at ha; subst a; trivial
  · exact checked1568
theorem derived1568 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1568 := by
  apply localUnsat_implies_entails f1568 [c1441, c1564, c1459, c1565, c1566, c309, c1567, c1254, c79, c66, c1218] c1568 unsat1568 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1459 := derived1459 a h
  have h3 : Entails.eval a c1565 := derived1565 a h
  have h4 : Entails.eval a c1566 := derived1566 a h
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c1567 := derived1567 a h
  have h7 : Entails.eval a c1254 := derived1254 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c1218 := derived1218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1569 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1569 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c248, some c139, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1569 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1569 : lratChecker f1569 p1569 = .success := by decide +kernel
theorem unsat1569 : Unsatisfiable (PosFin 31) f1569 := by
  apply lratCheckerSound f1569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1569
  · intro a ha; simp [p1569] at ha; subst a; trivial
  · exact checked1569
theorem derived1569 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1569 := by
  apply localUnsat_implies_entails f1569 [c86, c248, c139] c1569 unsat1569 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1570 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1570 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1534, some c1532, some c1569, some c1234, some c20, some c18, some c599, some c1260, some c311, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1570 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1570 : lratChecker f1570 p1570 = .success := by decide +kernel
theorem unsat1570 : Unsatisfiable (PosFin 31) f1570 := by
  apply lratCheckerSound f1570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1570
  · intro a ha; simp [p1570] at ha; subst a; trivial
  · exact checked1570
theorem derived1570 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1570 := by
  apply localUnsat_implies_entails f1570 [c1441, c1529, c1534, c1532, c1569, c1234, c20, c18, c599, c1260, c311] c1570 unsat1570 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1534 := derived1534 a h
  have h3 : Entails.eval a c1532 := derived1532 a h
  have h4 : Entails.eval a c1569 := derived1569 a h
  have h5 : Entails.eval a c1234 := derived1234 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c599 := h 598 (by decide)
  have h9 : Entails.eval a c1260 := derived1260 a h
  have h10 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1571 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1571 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1564, some c1529, some c1568, some c1534, some c1515, some c1532, some c1569, some c1570, some c28, some c268, some c327, some c1264, some c1247, some c101, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1571 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1571 : lratChecker f1571 p1571 = .success := by decide +kernel
theorem unsat1571 : Unsatisfiable (PosFin 31) f1571 := by
  apply lratCheckerSound f1571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1571
  · intro a ha; simp [p1571] at ha; subst a; trivial
  · exact checked1571
theorem derived1571 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1571 := by
  apply localUnsat_implies_entails f1571 [c1441, c1564, c1529, c1568, c1534, c1515, c1532, c1569, c1570, c28, c268, c327, c1264, c1247, c101] c1571 unsat1571 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1568 := derived1568 a h
  have h4 : Entails.eval a c1534 := derived1534 a h
  have h5 : Entails.eval a c1515 := derived1515 a h
  have h6 : Entails.eval a c1532 := derived1532 a h
  have h7 : Entails.eval a c1569 := derived1569 a h
  have h8 : Entails.eval a c1570 := derived1570 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c1264 := derived1264 a h
  have h13 : Entails.eval a c1247 := derived1247 a h
  have h14 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1572 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1572 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1534, some c1532, some c1564, some c1515, some c1571, some c28, some c268, some c327, some c213, some c1264, some c549, some c66, some c1207, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1572 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1572 : lratChecker f1572 p1572 = .success := by decide +kernel
theorem unsat1572 : Unsatisfiable (PosFin 31) f1572 := by
  apply lratCheckerSound f1572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1572
  · intro a ha; simp [p1572] at ha; subst a; trivial
  · exact checked1572
theorem derived1572 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1572 := by
  apply localUnsat_implies_entails f1572 [c1441, c1529, c1534, c1532, c1564, c1515, c1571, c28, c268, c327, c213, c1264, c549, c66, c1207] c1572 unsat1572 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1534 := derived1534 a h
  have h3 : Entails.eval a c1532 := derived1532 a h
  have h4 : Entails.eval a c1564 := derived1564 a h
  have h5 : Entails.eval a c1515 := derived1515 a h
  have h6 : Entails.eval a c1571 := derived1571 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c1264 := derived1264 a h
  have h12 : Entails.eval a c549 := h 548 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c1207 := derived1207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1573 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1573 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1571, some c1529, some c1534, some c1572, some c1303, some c1206, some c79, some c82, some c189, some c1204, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1573 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1573 : lratChecker f1573 p1573 = .success := by decide +kernel
theorem unsat1573 : Unsatisfiable (PosFin 31) f1573 := by
  apply lratCheckerSound f1573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1573
  · intro a ha; simp [p1573] at ha; subst a; trivial
  · exact checked1573
theorem derived1573 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1573 := by
  apply localUnsat_implies_entails f1573 [c1441, c1571, c1529, c1534, c1572, c1303, c1206, c79, c82, c189, c1204] c1573 unsat1573 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1571 := derived1571 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1534 := derived1534 a h
  have h4 : Entails.eval a c1572 := derived1572 a h
  have h5 : Entails.eval a c1303 := derived1303 a h
  have h6 : Entails.eval a c1206 := derived1206 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c1204 := derived1204 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1574 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1574 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1571, some c1564, some c1529, some c1303, some c669, some c65, some c1297, some c1300, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1574 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1574 : lratChecker f1574 p1574 = .success := by decide +kernel
theorem unsat1574 : Unsatisfiable (PosFin 31) f1574 := by
  apply lratCheckerSound f1574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1574
  · intro a ha; simp [p1574] at ha; subst a; trivial
  · exact checked1574
theorem derived1574 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1574 := by
  apply localUnsat_implies_entails f1574 [c1441, c1571, c1564, c1529, c1303, c669, c65, c1297, c1300] c1574 unsat1574 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1571 := derived1571 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1529 := derived1529 a h
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c669 := h 668 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1297 := derived1297 a h
  have h8 : Entails.eval a c1300 := derived1300 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1575 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1575 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1574, some c1564, some c1573, some c594, some c90, some c370, some c1571, some c591, some c769, some c352, some c491, some c7, some c28, some c157, some c519, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1575 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1575 : lratChecker f1575 p1575 = .success := by decide +kernel
theorem unsat1575 : Unsatisfiable (PosFin 31) f1575 := by
  apply lratCheckerSound f1575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1575
  · intro a ha; simp [p1575] at ha; subst a; trivial
  · exact checked1575
theorem derived1575 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1575 := by
  apply localUnsat_implies_entails f1575 [c1441, c1574, c1564, c1573, c594, c90, c370, c1571, c591, c769, c352, c491, c7, c28, c157, c519] c1575 unsat1575 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1573 := derived1573 a h
  have h4 : Entails.eval a c594 := h 593 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c1571 := derived1571 a h
  have h8 : Entails.eval a c591 := h 590 (by decide)
  have h9 : Entails.eval a c769 := h 768 (by decide)
  have h10 : Entails.eval a c352 := h 351 (by decide)
  have h11 : Entails.eval a c491 := h 490 (by decide)
  have h12 : Entails.eval a c7 := h 6 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c519 := h 518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1576 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1576 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1564, some c1529, some c1573, some c1574, some c594, some c90, some c370, some c1575, some c53, some c657, some c41, some c521, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1576 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1576 : lratChecker f1576 p1576 = .success := by decide +kernel
theorem unsat1576 : Unsatisfiable (PosFin 31) f1576 := by
  apply lratCheckerSound f1576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1576
  · intro a ha; simp [p1576] at ha; subst a; trivial
  · exact checked1576
theorem derived1576 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1576 := by
  apply localUnsat_implies_entails f1576 [c1441, c1564, c1529, c1573, c1574, c594, c90, c370, c1575, c53, c657, c41, c521] c1576 unsat1576 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1529 := derived1529 a h
  have h3 : Entails.eval a c1573 := derived1573 a h
  have h4 : Entails.eval a c1574 := derived1574 a h
  have h5 : Entails.eval a c594 := h 593 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c1575 := derived1575 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c657 := h 656 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1577 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1577 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c53, some c1576, some c1564, some c1478, some c253, some c1493, some c370, some c1497, some c1459, some c166, some c564, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1577 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1577 : lratChecker f1577 p1577 = .success := by decide +kernel
theorem unsat1577 : Unsatisfiable (PosFin 31) f1577 := by
  apply lratCheckerSound f1577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1577
  · intro a ha; simp [p1577] at ha; subst a; trivial
  · exact checked1577
theorem derived1577 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1577 := by
  apply localUnsat_implies_entails f1577 [c1441, c1529, c53, c1576, c1564, c1478, c253, c1493, c370, c1497, c1459, c166, c564] c1577 unsat1577 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c1576 := derived1576 a h
  have h4 : Entails.eval a c1564 := derived1564 a h
  have h5 : Entails.eval a c1478 := derived1478 a h
  have h6 : Entails.eval a c253 := h 252 (by decide)
  have h7 : Entails.eval a c1493 := derived1493 a h
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c1497 := derived1497 a h
  have h10 : Entails.eval a c1459 := derived1459 a h
  have h11 : Entails.eval a c166 := h 165 (by decide)
  have h12 : Entails.eval a c564 := h 563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1578 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1578 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1576, some c1529, some c1534, some c1221, some c1532, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1578 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1578 : lratChecker f1578 p1578 = .success := by decide +kernel
theorem unsat1578 : Unsatisfiable (PosFin 31) f1578 := by
  apply lratCheckerSound f1578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1578
  · intro a ha; simp [p1578] at ha; subst a; trivial
  · exact checked1578
theorem derived1578 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1578 := by
  apply localUnsat_implies_entails f1578 [c1576, c1529, c1534, c1221, c1532] c1578 unsat1578 (by rfl) a
  have h0 : Entails.eval a c1576 := derived1576 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1534 := derived1534 a h
  have h3 : Entails.eval a c1221 := derived1221 a h
  have h4 : Entails.eval a c1532 := derived1532 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1579 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1579 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1576, some c1564, some c1478, some c253, some c1577, some c722, some c370, some c352, some c500, some c353, some c417, some c1459, some c33, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1579 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1579 : lratChecker f1579 p1579 = .success := by decide +kernel
theorem unsat1579 : Unsatisfiable (PosFin 31) f1579 := by
  apply lratCheckerSound f1579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1579
  · intro a ha; simp [p1579] at ha; subst a; trivial
  · exact checked1579
theorem derived1579 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1579 := by
  apply localUnsat_implies_entails f1579 [c1441, c1578, c1576, c1564, c1478, c253, c1577, c722, c370, c352, c500, c353, c417, c1459, c33] c1579 unsat1579 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1478 := derived1478 a h
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c1577 := derived1577 a h
  have h7 : Entails.eval a c722 := h 721 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c500 := h 499 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c417 := h 416 (by decide)
  have h13 : Entails.eval a c1459 := derived1459 a h
  have h14 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1580 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1580 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1579, some c1576, some c1564, some c1318, some c65, some c110, some c1299, some c140, some c1216, some c1223, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1580 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1580 : lratChecker f1580 p1580 = .success := by decide +kernel
theorem unsat1580 : Unsatisfiable (PosFin 31) f1580 := by
  apply lratCheckerSound f1580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1580
  · intro a ha; simp [p1580] at ha; subst a; trivial
  · exact checked1580
theorem derived1580 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1580 := by
  apply localUnsat_implies_entails f1580 [c1441, c1579, c1576, c1564, c1318, c65, c110, c1299, c140, c1216, c1223] c1580 unsat1580 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1579 := derived1579 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1318 := derived1318 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1299 := derived1299 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c1216 := derived1216 a h
  have h10 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1581 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1581 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1580, some c1579, some c1576, some c1564, some c1278, some c298, some c1299, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1581 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1581 : lratChecker f1581 p1581 = .success := by decide +kernel
theorem unsat1581 : Unsatisfiable (PosFin 31) f1581 := by
  apply lratCheckerSound f1581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1581
  · intro a ha; simp [p1581] at ha; subst a; trivial
  · exact checked1581
theorem derived1581 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1581 := by
  apply localUnsat_implies_entails f1581 [c1580, c1579, c1576, c1564, c1278, c298, c1299] c1581 unsat1581 (by rfl) a
  have h0 : Entails.eval a c1580 := derived1580 a h
  have h1 : Entails.eval a c1579 := derived1579 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c1299 := derived1299 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1582 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1582 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1579, some c1576, some c1564, some c1580, some c1581, some c76, some c18, some c633, some c216, some c664, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1582 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1582 : lratChecker f1582 p1582 = .success := by decide +kernel
theorem unsat1582 : Unsatisfiable (PosFin 31) f1582 := by
  apply lratCheckerSound f1582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1582
  · intro a ha; simp [p1582] at ha; subst a; trivial
  · exact checked1582
theorem derived1582 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1582 := by
  apply localUnsat_implies_entails f1582 [c1441, c1579, c1576, c1564, c1580, c1581, c76, c18, c633, c216, c664] c1582 unsat1582 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1579 := derived1579 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1580 := derived1580 a h
  have h5 : Entails.eval a c1581 := derived1581 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c633 := h 632 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c664 := h 663 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1583 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1583 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1529, some c1564, some c1576, some c1578, some c1579, some c1582, some c53, some c1495, some c1204, some c1229, some c420, some c216, some c311, some c1256, some c1459, some c664, some c663, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1583 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1583 : lratChecker f1583 p1583 = .success := by decide +kernel
theorem unsat1583 : Unsatisfiable (PosFin 31) f1583 := by
  apply lratCheckerSound f1583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1583
  · intro a ha; simp [p1583] at ha; subst a; trivial
  · exact checked1583
theorem derived1583 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1583 := by
  apply localUnsat_implies_entails f1583 [c1441, c1529, c1564, c1576, c1578, c1579, c1582, c53, c1495, c1204, c1229, c420, c216, c311, c1256, c1459, c664, c663] c1583 unsat1583 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1529 := derived1529 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1576 := derived1576 a h
  have h4 : Entails.eval a c1578 := derived1578 a h
  have h5 : Entails.eval a c1579 := derived1579 a h
  have h6 : Entails.eval a c1582 := derived1582 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c1495 := derived1495 a h
  have h9 : Entails.eval a c1204 := derived1204 a h
  have h10 : Entails.eval a c1229 := derived1229 a h
  have h11 : Entails.eval a c420 := h 419 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c311 := h 310 (by decide)
  have h14 : Entails.eval a c1256 := derived1256 a h
  have h15 : Entails.eval a c1459 := derived1459 a h
  have h16 : Entails.eval a c664 := h 663 (by decide)
  have h17 : Entails.eval a c663 := h 662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1584 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1584 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1583, some c1495, some c1204, some c284, some c29, some c1203, some c16, some c189, some c287, some c142, some c119, some c82, some c280, some c505, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1584 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1584 : lratChecker f1584 p1584 = .success := by decide +kernel
theorem unsat1584 : Unsatisfiable (PosFin 31) f1584 := by
  apply lratCheckerSound f1584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1584
  · intro a ha; simp [p1584] at ha; subst a; trivial
  · exact checked1584
theorem derived1584 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1584 := by
  apply localUnsat_implies_entails f1584 [c1441, c1583, c1495, c1204, c284, c29, c1203, c16, c189, c287, c142, c119, c82, c280, c505] c1584 unsat1584 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1495 := derived1495 a h
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1203 := derived1203 a h
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c287 := h 286 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c505 := h 504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1585 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1585 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1583, some c1360, some c1204, some c79, some c188, some c1203, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1585 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1585 : lratChecker f1585 p1585 = .success := by decide +kernel
theorem unsat1585 : Unsatisfiable (PosFin 31) f1585 := by
  apply lratCheckerSound f1585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1585
  · intro a ha; simp [p1585] at ha; subst a; trivial
  · exact checked1585
theorem derived1585 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1585 := by
  apply localUnsat_implies_entails f1585 [c1441, c1583, c1360, c1204, c79, c188, c1203] c1585 unsat1585 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1360 := derived1360 a h
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1586 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1586 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1318, some c343, some c1278, some c18, some c76, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1586 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1586 : lratChecker f1586 p1586 = .success := by decide +kernel
theorem unsat1586 : Unsatisfiable (PosFin 31) f1586 := by
  apply lratCheckerSound f1586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1586
  · intro a ha; simp [p1586] at ha; subst a; trivial
  · exact checked1586
theorem derived1586 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1586 := by
  apply localUnsat_implies_entails f1586 [c1583, c1318, c343, c1278, c18, c76] c1586 unsat1586 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1318 := derived1318 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c1278 := derived1278 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1587 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1587 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1584, some c1585, some c1586, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1587 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1587 : lratChecker f1587 p1587 = .success := by decide +kernel
theorem unsat1587 : Unsatisfiable (PosFin 31) f1587 := by
  apply lratCheckerSound f1587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1587
  · intro a ha; simp [p1587] at ha; subst a; trivial
  · exact checked1587
theorem derived1587 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1587 := by
  apply localUnsat_implies_entails f1587 [c1584, c1585, c1586] c1587 unsat1587 (by rfl) a
  have h0 : Entails.eval a c1584 := derived1584 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1586 := derived1586 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1588 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1588 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c343, some c1587, some c76, some c819, some c17, some c79, some c81, some c292, some c491, some c242, some c1206, some c45, some c1212, some c593, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1588 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1588 : lratChecker f1588 p1588 = .success := by decide +kernel
theorem unsat1588 : Unsatisfiable (PosFin 31) f1588 := by
  apply lratCheckerSound f1588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1588
  · intro a ha; simp [p1588] at ha; subst a; trivial
  · exact checked1588
theorem derived1588 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1588 := by
  apply localUnsat_implies_entails f1588 [c1583, c1441, c343, c1587, c76, c819, c17, c79, c81, c292, c491, c242, c1206, c45, c1212, c593] c1588 unsat1588 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c819 := h 818 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c491 := h 490 (by decide)
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c1206 := derived1206 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c1212 := derived1212 a h
  have h15 : Entails.eval a c593 := h 592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1589 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1589 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1588, some c1587, some c292, some c28, some c30, some c811, some c241, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1589 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1589 : lratChecker f1589 p1589 = .success := by decide +kernel
theorem unsat1589 : Unsatisfiable (PosFin 31) f1589 := by
  apply lratCheckerSound f1589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1589
  · intro a ha; simp [p1589] at ha; subst a; trivial
  · exact checked1589
theorem derived1589 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1589 := by
  apply localUnsat_implies_entails f1589 [c1588, c1587, c292, c28, c30, c811, c241] c1589 unsat1589 (by rfl) a
  have h0 : Entails.eval a c1588 := derived1588 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c811 := h 810 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1590 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1590 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1587, some c1221, some c253, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1590 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1590 : lratChecker f1590 p1590 = .success := by decide +kernel
theorem unsat1590 : Unsatisfiable (PosFin 31) f1590 := by
  apply lratCheckerSound f1590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1590
  · intro a ha; simp [p1590] at ha; subst a; trivial
  · exact checked1590
theorem derived1590 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1590 := by
  apply localUnsat_implies_entails f1590 [c1587, c1221, c253] c1590 unsat1590 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1591 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1591 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c343, some c1590, some c1589, some c17, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1591 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1591 : lratChecker f1591 p1591 = .success := by decide +kernel
theorem unsat1591 : Unsatisfiable (PosFin 31) f1591 := by
  apply lratCheckerSound f1591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1591
  · intro a ha; simp [p1591] at ha; subst a; trivial
  · exact checked1591
theorem derived1591 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1591 := by
  apply localUnsat_implies_entails f1591 [c1583, c343, c1590, c1589, c17] c1591 unsat1591 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1589 := derived1589 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1592 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1592 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c1591, some c343, some c1590, some c1587, some c1275, some c913, some c74, some c839, some c728, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1592 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1592 : lratChecker f1592 p1592 = .success := by decide +kernel
theorem unsat1592 : Unsatisfiable (PosFin 31) f1592 := by
  apply lratCheckerSound f1592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1592
  · intro a ha; simp [p1592] at ha; subst a; trivial
  · exact checked1592
theorem derived1592 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1592 := by
  apply localUnsat_implies_entails f1592 [c1583, c1441, c1591, c343, c1590, c1587, c1275, c913, c74, c839, c728] c1592 unsat1592 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1591 := derived1591 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c1587 := derived1587 a h
  have h6 : Entails.eval a c1275 := derived1275 a h
  have h7 : Entails.eval a c913 := h 912 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c839 := h 838 (by decide)
  have h10 : Entails.eval a c728 := h 727 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1593 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1593 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1590, some c1587, some c1591, some c1592, some c292, some c490, some c293, some c1223, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1593 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1593 : lratChecker f1593 p1593 = .success := by decide +kernel
theorem unsat1593 : Unsatisfiable (PosFin 31) f1593 := by
  apply lratCheckerSound f1593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1593
  · intro a ha; simp [p1593] at ha; subst a; trivial
  · exact checked1593
theorem derived1593 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1593 := by
  apply localUnsat_implies_entails f1593 [c1590, c1587, c1591, c1592, c292, c490, c293, c1223] c1593 unsat1593 (by rfl) a
  have h0 : Entails.eval a c1590 := derived1590 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1591 := derived1591 a h
  have h3 : Entails.eval a c1592 := derived1592 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c490 := h 489 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1594 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1593, some c1587, some c292, some c28, some c296, some c352, some c295, some c241, some c81, some c1266, some c733, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1594 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 31) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c1441, c1593, c1587, c292, c28, c296, c352, c295, c241, c81, c1266, c733] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1593 := derived1593 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c292 := h 291 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c296 := h 295 (by decide)
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c1266 := derived1266 a h
  have h11 : Entails.eval a c733 := h 732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c252, some c90, some c1253, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1595 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 31) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c1583, c1441, c252, c90, c1253] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c53, some c313, some c1253, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1596 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 31) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c1583, c53, c313, c1253] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c1253 := derived1253 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨4, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1595, some c1596, some c1207, some c458, some c885, some c1459, some c799, some c1265, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1597 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 31) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c1595, c1596, c1207, c458, c885, c1459, c799, c1265] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c1595 := derived1595 a h
  have h1 : Entails.eval a c1596 := derived1596 a h
  have h2 : Entails.eval a c1207 := derived1207 a h
  have h3 : Entails.eval a c458 := h 457 (by decide)
  have h4 : Entails.eval a c885 := h 884 (by decide)
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c799 := h 798 (by decide)
  have h7 : Entails.eval a c1265 := derived1265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c134, some c81, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1598 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 31) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1441, c134, c81] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1593, some c1598, some c1590, some c1594, some c1597, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1599 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 31) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1593, c1598, c1590, c1594, c1597] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1593 := derived1593 a h
  have h1 : Entails.eval a c1598 := derived1598 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1594 := derived1594 a h
  have h4 : Entails.eval a c1597 := derived1597 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1600 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1598, some c17, some c1596, some c284, some c29, some c458, some c885, some c799, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1600 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 31) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1583, c1598, c17, c1596, c284, c29, c458, c885, c799] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1598 := derived1598 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c1596 := derived1596 a h
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c458 := h 457 (by decide)
  have h7 : Entails.eval a c885 := h 884 (by decide)
  have h8 : Entails.eval a c799 := h 798 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1590, some c1587, some c1593, some c1598, some c1599, some c1600, some c292, some c28, some c352, some c241, some c516, some c537, some c53, some c1411, some c1207, some c1459, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1601 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 31) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1583, c1590, c1587, c1593, c1598, c1599, c1600, c292, c28, c352, c241, c516, c537, c53, c1411, c1207, c1459] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1590 := derived1590 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1593 := derived1593 a h
  have h4 : Entails.eval a c1598 := derived1598 a h
  have h5 : Entails.eval a c1599 := derived1599 a h
  have h6 : Entails.eval a c1600 := derived1600 a h
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c516 := h 515 (by decide)
  have h12 : Entails.eval a c537 := h 536 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c1411 := derived1411 a h
  have h15 : Entails.eval a c1207 := derived1207 a h
  have h16 : Entails.eval a c1459 := derived1459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1601, some c1590, some c1587, some c292, some c28, some c352, some c241, some c864, some c21, some c82, some c243, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1602 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 31) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c1441, c1601, c1590, c1587, c292, c28, c352, c241, c864, c21, c82, c243] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c864 := h 863 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1601, some c1590, some c1602, some c17, some c232, some c1587, some c57, some c1263, some c1312, some c883, some c782, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1603 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 31) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1583, c1601, c1590, c1602, c17, c232, c1587, c57, c1263, c1312, c883, c782] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1602 := derived1602 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c1587 := derived1587 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c1263 := derived1263 a h
  have h9 : Entails.eval a c1312 := derived1312 a h
  have h10 : Entails.eval a c883 := h 882 (by decide)
  have h11 : Entails.eval a c782 := h 781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1601, some c1590, some c1602, some c17, some c29, some c232, some c1603, some c1245, some c889, some c1214, some c1290, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1604 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 31) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1583, c1601, c1590, c1602, c17, c29, c232, c1603, c1245, c889, c1214, c1290] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1602 := derived1602 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c1603 := derived1603 a h
  have h8 : Entails.eval a c1245 := derived1245 a h
  have h9 : Entails.eval a c889 := h 888 (by decide)
  have h10 : Entails.eval a c1214 := derived1214 a h
  have h11 : Entails.eval a c1290 := derived1290 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1605 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c460, some c1276, some c1277, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1605 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 31) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c460, c1276, c1277] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c460 := h 459 (by decide)
  have h1 : Entails.eval a c1276 := derived1276 a h
  have h2 : Entails.eval a c1277 := derived1277 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1604, some c1601, some c1590, some c37, some c257, some c1605, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1606 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 31) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1604, c1601, c1590, c37, c257, c1605] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1604 := derived1604 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c1605 := derived1605 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1583, some c1606, some c1604, some c1590, some c527, some c718, some c1595, some c1315, some c29, some c931, some c540, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1607 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 31) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1441, c1583, c1606, c1604, c1590, c527, c718, c1595, c1315, c29, c931, c540] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1606 := derived1606 a h
  have h3 : Entails.eval a c1604 := derived1604 a h
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c527 := h 526 (by decide)
  have h6 : Entails.eval a c718 := h 717 (by decide)
  have h7 : Entails.eval a c1595 := derived1595 a h
  have h8 : Entails.eval a c1315 := derived1315 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c931 := derived931 a h
  have h11 : Entails.eval a c540 := h 539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1606, some c1604, some c1601, some c1590, some c1587, some c273, some c335, some c1311, some c883, some c782, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1608 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 31) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1583, c1606, c1604, c1601, c1590, c1587, c273, c335, c1311, c883, c782] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1606 := derived1606 a h
  have h2 : Entails.eval a c1604 := derived1604 a h
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c1587 := derived1587 a h
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c1311 := derived1311 a h
  have h9 : Entails.eval a c883 := h 882 (by decide)
  have h10 : Entails.eval a c782 := h 781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1608, some c1607, some c1604, some c1601, some c1590, some c1587, some c1459, some c1497, some c1220, some c369, some c904, some c1053, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 31) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1441, c1608, c1607, c1604, c1601, c1590, c1587, c1459, c1497, c1220, c369, c904, c1053] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1608 := derived1608 a h
  have h2 : Entails.eval a c1607 := derived1607 a h
  have h3 : Entails.eval a c1604 := derived1604 a h
  have h4 : Entails.eval a c1601 := derived1601 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c1587 := derived1587 a h
  have h7 : Entails.eval a c1459 := derived1459 a h
  have h8 : Entails.eval a c1497 := derived1497 a h
  have h9 : Entails.eval a c1220 := derived1220 a h
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c904 := h 903 (by decide)
  have h12 : Entails.eval a c1053 := derived1053 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1610 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1608, some c1606, some c1604, some c1601, some c1590, some c1609, some c1534, some c817, some c1605, some c736, some c464, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1610 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 31) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1608, c1606, c1604, c1601, c1590, c1609, c1534, c817, c1605, c736, c464] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1608 := derived1608 a h
  have h1 : Entails.eval a c1606 := derived1606 a h
  have h2 : Entails.eval a c1604 := derived1604 a h
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c1609 := derived1609 a h
  have h6 : Entails.eval a c1534 := derived1534 a h
  have h7 : Entails.eval a c817 := h 816 (by decide)
  have h8 : Entails.eval a c1605 := derived1605 a h
  have h9 : Entails.eval a c736 := h 735 (by decide)
  have h10 : Entails.eval a c464 := h 463 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1604, some c1601, some c1587, some c79, some c780, some c135, some c1207, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1611 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 31) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1441, c1604, c1601, c1587, c79, c780, c135, c1207] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1604 := derived1604 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c780 := h 779 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c1207 := derived1207 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1587, some c1590, some c1601, some c1604, some c1611, some c1610, some c292, some c28, some c352, some c241, some c21, some c694, some c931, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1612 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 31) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c1587, c1590, c1601, c1604, c1611, c1610, c292, c28, c352, c241, c21, c694, c931] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1590 := derived1590 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c1604 := derived1604 a h
  have h4 : Entails.eval a c1611 := derived1611 a h
  have h5 : Entails.eval a c1610 := derived1610 a h
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c694 := h 693 (by decide)
  have h12 : Entails.eval a c931 := derived931 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1613 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1613 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1534, some c1294, some c1513, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1613 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1613 : lratChecker f1613 p1613 = .success := by decide +kernel
theorem unsat1613 : Unsatisfiable (PosFin 31) f1613 := by
  apply lratCheckerSound f1613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1613
  · intro a ha; simp [p1613] at ha; subst a; trivial
  · exact checked1613
theorem derived1613 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1613 := by
  apply localUnsat_implies_entails f1613 [c1612, c1534, c1294, c1513] c1613 unsat1613 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1534 := derived1534 a h
  have h2 : Entails.eval a c1294 := derived1294 a h
  have h3 : Entails.eval a c1513 := derived1513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1614 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1614 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c110, some c1053, some c521, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1614 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1614 : lratChecker f1614 p1614 = .success := by decide +kernel
theorem unsat1614 : Unsatisfiable (PosFin 31) f1614 := by
  apply lratCheckerSound f1614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1614
  · intro a ha; simp [p1614] at ha; subst a; trivial
  · exact checked1614
theorem derived1614 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1614 := by
  apply localUnsat_implies_entails f1614 [c1441, c1612, c110, c1053, c521] c1614 unsat1614 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1053 := derived1053 a h
  have h4 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1615 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1615 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1583, some c1585, some c28, some c1613, some c7, some c1614, some c1513, some c252, some c307, some c297, some c14, some c335, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1615 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1615 : lratChecker f1615 p1615 = .success := by decide +kernel
theorem unsat1615 : Unsatisfiable (PosFin 31) f1615 := by
  apply lratCheckerSound f1615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1615
  · intro a ha; simp [p1615] at ha; subst a; trivial
  · exact checked1615
theorem derived1615 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1615 := by
  apply localUnsat_implies_entails f1615 [c1612, c1583, c1585, c28, c1613, c7, c1614, c1513, c252, c307, c297, c14, c335] c1615 unsat1615 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1613 := derived1613 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c1614 := derived1614 a h
  have h7 : Entails.eval a c1513 := derived1513 a h
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1616 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1616 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c1441, some c1615, some c252, some c297, some c81, some c492, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1616 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1616 : lratChecker f1616 p1616 = .success := by decide +kernel
theorem unsat1616 : Unsatisfiable (PosFin 31) f1616 := by
  apply lratCheckerSound f1616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1616
  · intro a ha; simp [p1616] at ha; subst a; trivial
  · exact checked1616
theorem derived1616 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1616 := by
  apply localUnsat_implies_entails f1616 [c1583, c1612, c1441, c1615, c252, c297, c81, c492] c1616 unsat1616 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1615 := derived1615 a h
  have h4 : Entails.eval a c252 := h 251 (by decide)
  have h5 : Entails.eval a c297 := h 296 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c492 := h 491 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1616

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
