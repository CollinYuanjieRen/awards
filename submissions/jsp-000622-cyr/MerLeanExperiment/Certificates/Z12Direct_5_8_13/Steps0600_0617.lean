import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Steps0500_0599

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1503 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1503 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1328, some c1441, some c1501, some c1495, some c148, some c1502, some c50, some c65, some c525, some c717, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1503 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1503 : lratChecker f1503 p1503 = .success := by decide +kernel
theorem unsat1503 : Unsatisfiable (PosFin 31) f1503 := by
  apply lratCheckerSound f1503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1503
  · intro a ha; simp [p1503] at ha; subst a; trivial
  · exact checked1503
theorem derived1503 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1503 := by
  apply localUnsat_implies_entails f1503 [c1328, c1441, c1501, c1495, c148, c1502, c50, c65, c525, c717] c1503 unsat1503 (by rfl) a
  have h0 : Entails.eval a c1328 := derived1328 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1501 := derived1501 a h
  have h3 : Entails.eval a c1495 := derived1495 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c1502 := derived1502 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c525 := h 524 (by decide)
  have h9 : Entails.eval a c717 := h 716 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1504 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1504 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1485, some c1441, some c1246, some c1328, some c1503, some c1501, some c1495, some c65, some c190, some c530, some c92, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1504 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1504 : lratChecker f1504 p1504 = .success := by decide +kernel
theorem unsat1504 : Unsatisfiable (PosFin 31) f1504 := by
  apply lratCheckerSound f1504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1504
  · intro a ha; simp [p1504] at ha; subst a; trivial
  · exact checked1504
theorem derived1504 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1504 := by
  apply localUnsat_implies_entails f1504 [c1440, c1485, c1441, c1246, c1328, c1503, c1501, c1495, c65, c190, c530, c92] c1504 unsat1504 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1485 := derived1485 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c1328 := derived1328 a h
  have h5 : Entails.eval a c1503 := derived1503 a h
  have h6 : Entails.eval a c1501 := derived1501 a h
  have h7 : Entails.eval a c1495 := derived1495 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c530 := h 529 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1505 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1505 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1246, some c1328, some c1441, some c1495, some c1501, some c1503, some c1504, some c50, some c27, some c195, some c1488, some c302, some c92, some c883, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1505 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1505 : lratChecker f1505 p1505 = .success := by decide +kernel
theorem unsat1505 : Unsatisfiable (PosFin 31) f1505 := by
  apply lratCheckerSound f1505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1505
  · intro a ha; simp [p1505] at ha; subst a; trivial
  · exact checked1505
theorem derived1505 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1505 := by
  apply localUnsat_implies_entails f1505 [c1485, c1246, c1328, c1441, c1495, c1501, c1503, c1504, c50, c27, c195, c1488, c302, c92, c883] c1505 unsat1505 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1328 := derived1328 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1495 := derived1495 a h
  have h5 : Entails.eval a c1501 := derived1501 a h
  have h6 : Entails.eval a c1503 := derived1503 a h
  have h7 : Entails.eval a c1504 := derived1504 a h
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c1488 := derived1488 a h
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c883 := h 882 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1506 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1506 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1505, some c1246, some c1485, some c38, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1506 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1506 : lratChecker f1506 p1506 = .success := by decide +kernel
theorem unsat1506 : Unsatisfiable (PosFin 31) f1506 := by
  apply lratCheckerSound f1506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1506
  · intro a ha; simp [p1506] at ha; subst a; trivial
  · exact checked1506
theorem derived1506 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1506 := by
  apply localUnsat_implies_entails f1506 [c1505, c1246, c1485, c38] c1506 unsat1506 (by rfl) a
  have h0 : Entails.eval a c1505 := derived1505 a h
  have h1 : Entails.eval a c1246 := derived1246 a h
  have h2 : Entails.eval a c1485 := derived1485 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1507 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1507 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1485, some c1505, some c1440, some c1246, some c1441, some c1506, some c37, some c1381, some c1473, some c718, some c421, some c192, some c881, some c208, some c301, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1507 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1507 : lratChecker f1507 p1507 = .success := by decide +kernel
theorem unsat1507 : Unsatisfiable (PosFin 31) f1507 := by
  apply lratCheckerSound f1507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1507
  · intro a ha; simp [p1507] at ha; subst a; trivial
  · exact checked1507
theorem derived1507 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1507 := by
  apply localUnsat_implies_entails f1507 [c1485, c1505, c1440, c1246, c1441, c1506, c37, c1381, c1473, c718, c421, c192, c881, c208, c301] c1507 unsat1507 (by rfl) a
  have h0 : Entails.eval a c1485 := derived1485 a h
  have h1 : Entails.eval a c1505 := derived1505 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c1441 := derived1441 a h
  have h5 : Entails.eval a c1506 := derived1506 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1381 := derived1381 a h
  have h8 : Entails.eval a c1473 := derived1473 a h
  have h9 : Entails.eval a c718 := h 717 (by decide)
  have h10 : Entails.eval a c421 := h 420 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c881 := h 880 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1508 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1508 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1506, some c1498, some c206, some c208, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1508 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1508 : lratChecker f1508 p1508 = .success := by decide +kernel
theorem unsat1508 : Unsatisfiable (PosFin 31) f1508 := by
  apply lratCheckerSound f1508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1508
  · intro a ha; simp [p1508] at ha; subst a; trivial
  · exact checked1508
theorem derived1508 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1508 := by
  apply localUnsat_implies_entails f1508 [c1440, c1506, c1498, c206, c208] c1508 unsat1508 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1506 := derived1506 a h
  have h2 : Entails.eval a c1498 := derived1498 a h
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1509 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1509 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1506, some c1440, some c1505, some c1246, some c37, some c1508, some c1507, some c94, some c135, some c506, some c692, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1509 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1509 : lratChecker f1509 p1509 = .success := by decide +kernel
theorem unsat1509 : Unsatisfiable (PosFin 31) f1509 := by
  apply lratCheckerSound f1509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1509
  · intro a ha; simp [p1509] at ha; subst a; trivial
  · exact checked1509
theorem derived1509 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1509 := by
  apply localUnsat_implies_entails f1509 [c1506, c1440, c1505, c1246, c37, c1508, c1507, c94, c135, c506, c692] c1509 unsat1509 (by rfl) a
  have h0 : Entails.eval a c1506 := derived1506 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1508 := derived1508 a h
  have h6 : Entails.eval a c1507 := derived1507 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c506 := h 505 (by decide)
  have h10 : Entails.eval a c692 := h 691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1510 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1510 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1440, some c1506, some c94, some c87, some c135, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1510 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1510 : lratChecker f1510 p1510 = .success := by decide +kernel
theorem unsat1510 : Unsatisfiable (PosFin 31) f1510 := by
  apply lratCheckerSound f1510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1510
  · intro a ha; simp [p1510] at ha; subst a; trivial
  · exact checked1510
theorem derived1510 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1510 := by
  apply localUnsat_implies_entails f1510 [c1440, c1506, c94, c87, c135] c1510 unsat1510 (by rfl) a
  have h0 : Entails.eval a c1440 := derived1440 a h
  have h1 : Entails.eval a c1506 := derived1506 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1511 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1511 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1506, some c1440, some c1505, some c1246, some c1510, some c94, some c506, some c692, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1511 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1511 : lratChecker f1511 p1511 = .success := by decide +kernel
theorem unsat1511 : Unsatisfiable (PosFin 31) f1511 := by
  apply lratCheckerSound f1511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1511
  · intro a ha; simp [p1511] at ha; subst a; trivial
  · exact checked1511
theorem derived1511 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1511 := by
  apply localUnsat_implies_entails f1511 [c1506, c1440, c1505, c1246, c1510, c94, c506, c692] c1511 unsat1511 (by rfl) a
  have h0 : Entails.eval a c1506 := derived1506 a h
  have h1 : Entails.eval a c1440 := derived1440 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c1510 := derived1510 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c506 := h 505 (by decide)
  have h7 : Entails.eval a c692 := h 691 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1512 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1512 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1246, some c1505, some c1440, some c1506, some c1509, some c94, some c1510, some c1511, some c1498, some c1508, some c698, some c60, some c466, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1512 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1512 : lratChecker f1512 p1512 = .success := by decide +kernel
theorem unsat1512 : Unsatisfiable (PosFin 31) f1512 := by
  apply lratCheckerSound f1512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1512
  · intro a ha; simp [p1512] at ha; subst a; trivial
  · exact checked1512
theorem derived1512 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1512 := by
  apply localUnsat_implies_entails f1512 [c1246, c1505, c1440, c1506, c1509, c94, c1510, c1511, c1498, c1508, c698, c60, c466] c1512 unsat1512 (by rfl) a
  have h0 : Entails.eval a c1246 := derived1246 a h
  have h1 : Entails.eval a c1505 := derived1505 a h
  have h2 : Entails.eval a c1440 := derived1440 a h
  have h3 : Entails.eval a c1506 := derived1506 a h
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c1510 := derived1510 a h
  have h7 : Entails.eval a c1511 := derived1511 a h
  have h8 : Entails.eval a c1498 := derived1498 a h
  have h9 : Entails.eval a c1508 := derived1508 a h
  have h10 : Entails.eval a c698 := h 697 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c466 := h 465 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1513 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1513 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1506, some c1441, some c1505, some c1246, some c1328, some c1509, some c1512, some c1498, some c305, some c674, some c652, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1513 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1513 : lratChecker f1513 p1513 = .success := by decide +kernel
theorem unsat1513 : Unsatisfiable (PosFin 31) f1513 := by
  apply lratCheckerSound f1513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1513
  · intro a ha; simp [p1513] at ha; subst a; trivial
  · exact checked1513
theorem derived1513 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1513 := by
  apply localUnsat_implies_entails f1513 [c1506, c1441, c1505, c1246, c1328, c1509, c1512, c1498, c305, c674, c652] c1513 unsat1513 (by rfl) a
  have h0 : Entails.eval a c1506 := derived1506 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c1328 := derived1328 a h
  have h5 : Entails.eval a c1509 := derived1509 a h
  have h6 : Entails.eval a c1512 := derived1512 a h
  have h7 : Entails.eval a c1498 := derived1498 a h
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c674 := h 673 (by decide)
  have h10 : Entails.eval a c652 := h 651 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1514 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1514 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1513, some c1505, some c1473, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1514 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1514 : lratChecker f1514 p1514 = .success := by decide +kernel
theorem unsat1514 : Unsatisfiable (PosFin 31) f1514 := by
  apply lratCheckerSound f1514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1514
  · intro a ha; simp [p1514] at ha; subst a; trivial
  · exact checked1514
theorem derived1514 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1514 := by
  apply localUnsat_implies_entails f1514 [c1513, c1505, c1473] c1514 unsat1514 (by rfl) a
  have h0 : Entails.eval a c1513 := derived1513 a h
  have h1 : Entails.eval a c1505 := derived1505 a h
  have h2 : Entails.eval a c1473 := derived1473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1515 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1515 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1513, some c1506, some c1441, some c212, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1515 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1515 : lratChecker f1515 p1515 = .success := by decide +kernel
theorem unsat1515 : Unsatisfiable (PosFin 31) f1515 := by
  apply lratCheckerSound f1515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1515
  · intro a ha; simp [p1515] at ha; subst a; trivial
  · exact checked1515
theorem derived1515 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1515 := by
  apply localUnsat_implies_entails f1515 [c1513, c1506, c1441, c212] c1515 unsat1515 (by rfl) a
  have h0 : Entails.eval a c1513 := derived1513 a h
  have h1 : Entails.eval a c1506 := derived1506 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1516 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1516 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1513, some c1512, some c1441, some c1505, some c1246, some c718, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1516 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1516 : lratChecker f1516 p1516 = .success := by decide +kernel
theorem unsat1516 : Unsatisfiable (PosFin 31) f1516 := by
  apply lratCheckerSound f1516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1516
  · intro a ha; simp [p1516] at ha; subst a; trivial
  · exact checked1516
theorem derived1516 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1516 := by
  apply localUnsat_implies_entails f1516 [c1513, c1512, c1441, c1505, c1246, c718] c1516 unsat1516 (by rfl) a
  have h0 : Entails.eval a c1513 := derived1513 a h
  have h1 : Entails.eval a c1512 := derived1512 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1505 := derived1505 a h
  have h4 : Entails.eval a c1246 := derived1246 a h
  have h5 : Entails.eval a c718 := h 717 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1517 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1517 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1514, some c1513, some c1505, some c1441, some c1246, some c421, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1517 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1517 : lratChecker f1517 p1517 = .success := by decide +kernel
theorem unsat1517 : Unsatisfiable (PosFin 31) f1517 := by
  apply lratCheckerSound f1517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1517
  · intro a ha; simp [p1517] at ha; subst a; trivial
  · exact checked1517
theorem derived1517 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1517 := by
  apply localUnsat_implies_entails f1517 [c1514, c1513, c1505, c1441, c1246, c421] c1517 unsat1517 (by rfl) a
  have h0 : Entails.eval a c1514 := derived1514 a h
  have h1 : Entails.eval a c1513 := derived1513 a h
  have h2 : Entails.eval a c1505 := derived1505 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1246 := derived1246 a h
  have h5 : Entails.eval a c421 := h 420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1518 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1518 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1516, some c1513, some c1515, some c1517, some c1441, some c881, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1518 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1518 : lratChecker f1518 p1518 = .success := by decide +kernel
theorem unsat1518 : Unsatisfiable (PosFin 31) f1518 := by
  apply lratCheckerSound f1518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1518
  · intro a ha; simp [p1518] at ha; subst a; trivial
  · exact checked1518
theorem derived1518 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1518 := by
  apply localUnsat_implies_entails f1518 [c1516, c1513, c1515, c1517, c1441, c881] c1518 unsat1518 (by rfl) a
  have h0 : Entails.eval a c1516 := derived1516 a h
  have h1 : Entails.eval a c1513 := derived1513 a h
  have h2 : Entails.eval a c1515 := derived1515 a h
  have h3 : Entails.eval a c1517 := derived1517 a h
  have h4 : Entails.eval a c1441 := derived1441 a h
  have h5 : Entails.eval a c881 := h 880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1519 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1519 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1518, some c1506, some c1509, some c312, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1519 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1519 : lratChecker f1519 p1519 = .success := by decide +kernel
theorem unsat1519 : Unsatisfiable (PosFin 31) f1519 := by
  apply lratCheckerSound f1519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1519
  · intro a ha; simp [p1519] at ha; subst a; trivial
  · exact checked1519
theorem derived1519 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1519 := by
  apply localUnsat_implies_entails f1519 [c1518, c1506, c1509, c312] c1519 unsat1519 (by rfl) a
  have h0 : Entails.eval a c1518 := derived1518 a h
  have h1 : Entails.eval a c1506 := derived1506 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1520 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f1520 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1518, some c1519, some c1509, some c1514, some c266]
def p1520 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1520 : lratChecker f1520 p1520 = .success := by decide +kernel
theorem unsat1520 : Unsatisfiable (PosFin 31) f1520 := by
  apply lratCheckerSound f1520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1520
  · intro a ha; simp [p1520] at ha; subst a; trivial
  · exact checked1520
theorem derived1520 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1520 := by
  apply localUnsat_implies_entails f1520 [c1518, c1519, c1509, c1514, c266] c1520 unsat1520 (by rfl) a
  have h0 : Entails.eval a c1518 := derived1518 a h
  have h1 : Entails.eval a c1519 := derived1519 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c1514 := derived1514 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1520

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
