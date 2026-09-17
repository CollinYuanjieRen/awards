import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps1100_1199

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1619 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1598, some c1618, some c65, some c368, some c1525, some c367, some c371, some c150, some c79, some c13, some c104, some c153, some c1614, some c813, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 57) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c1441, c1578, c1598, c1618, c65, c368, c1525, c367, c371, c150, c79, c13, c104, c153, c1614, c813] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1598 := derived1598 a h
  have h3 : Entails.eval a c1618 := derived1618 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c1525 := derived1525 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c1614 := derived1614 a h
  have h15 : Entails.eval a c813 := derived813 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1620 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1619, some c1307, some c882, some c364, some c368, some c357, some c98, some c99, some c88, some c91, some c379, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 57) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c1441, c1578, c1619, c1307, c882, c364, c368, c357, c98, c99, c88, c91, c379] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c298, some c342, some c39, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 57) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c298, c342, c39] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c298 := h 297 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1619, some c882, some c1372, some c69, some c78, some c1620, some c1307, some c364, some c368, some c357, some c96, some c441, some c442, some c1621, some c818, some c90, some c377, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 57) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1578, c1441, c1619, c882, c1372, c69, c78, c1620, c1307, c364, c368, c357, c96, c441, c442, c1621, c818, c90, c377] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c882 := derived882 a h
  have h4 : Entails.eval a c1372 := derived1372 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c1620 := derived1620 a h
  have h8 : Entails.eval a c1307 := derived1307 a h
  have h9 : Entails.eval a c364 := h 363 (by decide)
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c441 := derived441 a h
  have h14 : Entails.eval a c442 := derived442 a h
  have h15 : Entails.eval a c1621 := derived1621 a h
  have h16 : Entails.eval a c818 := derived818 a h
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1619, some c1307, some c882, some c364, some c368, some c357, some c1620, some c1596, some c1372, some c1282, some c78, some c1622, some c88, some c91, some c1591, some c958, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 57) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c1441, c1578, c1619, c1307, c882, c364, c368, c357, c1620, c1596, c1372, c1282, c78, c1622, c88, c91, c1591, c958] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c1620 := derived1620 a h
  have h9 : Entails.eval a c1596 := derived1596 a h
  have h10 : Entails.eval a c1372 := derived1372 a h
  have h11 : Entails.eval a c1282 := derived1282 a h
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c1622 := derived1622 a h
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c1591 := derived1591 a h
  have h17 : Entails.eval a c958 := derived958 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1282, some c1623, some c102, some c1619, some c1307, some c882, some c364, some c368, some c357, some c1620, some c1596, some c780, some c1609, some c377, some c86, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 57) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1578, c1282, c1623, c102, c1619, c1307, c882, c364, c368, c357, c1620, c1596, c780, c1609, c377, c86] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1623 := derived1623 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c1619 := derived1619 a h
  have h5 : Entails.eval a c1307 := derived1307 a h
  have h6 : Entails.eval a c882 := derived882 a h
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c1620 := derived1620 a h
  have h11 : Entails.eval a c1596 := derived1596 a h
  have h12 : Entails.eval a c780 := derived780 a h
  have h13 : Entails.eval a c1609 := derived1609 a h
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1282, some c1619, some c882, some c1307, some c1372, some c364, some c154, some c368, some c357, some c1620, some c1596, some c1623, some c15, some c155, some c1624, some c1050, some c178, some c88, some c91, some c377, some c17, some c168, some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 57) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1441, c1578, c1282, c1619, c882, c1307, c1372, c364, c154, c368, c357, c1620, c1596, c1623, c15, c155, c1624, c1050, c178, c88, c91, c377, c17, c168] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1619 := derived1619 a h
  have h4 : Entails.eval a c882 := derived882 a h
  have h5 : Entails.eval a c1307 := derived1307 a h
  have h6 : Entails.eval a c1372 := derived1372 a h
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c1620 := derived1620 a h
  have h12 : Entails.eval a c1596 := derived1596 a h
  have h13 : Entails.eval a c1623 := derived1623 a h
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c1624 := derived1624 a h
  have h17 : Entails.eval a c1050 := derived1050 a h
  have h18 : Entails.eval a c178 := h 177 (by decide)
  have h19 : Entails.eval a c88 := h 87 (by decide)
  have h20 : Entails.eval a c91 := h 90 (by decide)
  have h21 : Entails.eval a c377 := h 376 (by decide)
  have h22 : Entails.eval a c17 := h 16 (by decide)
  have h23 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c67, some c364, some c375, some c363, some c381, some c1380, some c1379, some c182, some c185, some c157, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 57) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1441, c1578, c1625, c67, c364, c375, c363, c381, c1380, c1379, c182, c185, c157] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c1380 := derived1380 a h
  have h9 : Entails.eval a c1379 := derived1379 a h
  have h10 : Entails.eval a c182 := h 181 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c67, some c366, some c1380, some c1379, some c375, some c182, some c185, some c157, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 57) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1441, c1578, c1625, c67, c366, c1380, c1379, c375, c182, c185, c157] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c1380 := derived1380 a h
  have h6 : Entails.eval a c1379 := derived1379 a h
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨47, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c13, some c539, some c158, some c105, some c178, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 57) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1625, c13, c539, c158, c105, c178] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c669, some c1627, some c381, some c571, some c570, some c193, some c247, some c238, some c1628, some c174, some c173, some c170, some c185, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 57) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c1441, c1578, c669, c1627, c381, c571, c570, c193, c247, c238, c1628, c174, c173, c170, c185] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c669 := derived669 a h
  have h3 : Entails.eval a c1627 := derived1627 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c571 := derived571 a h
  have h6 : Entails.eval a c570 := derived570 a h
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c1628 := derived1628 a h
  have h11 : Entails.eval a c174 := h 173 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1626, some c1629, some c1164, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 57) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c1626, c1629, c1164] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c1626 := derived1626 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1164 := derived1164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1625, some c1578, some c669, some c1630, some c813, some c384, some c359, some c66, some c148, some c1164, some c422, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 57) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c1441, c1625, c1578, c669, c1630, c813, c384, c359, c66, c148, c1164, c422] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c669 := derived669 a h
  have h4 : Entails.eval a c1630 := derived1630 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1164 := derived1164 a h
  have h11 : Entails.eval a c422 := derived422 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c1578, some c1631, some c379, some c377, some c569, some c358, some c66, some c148, some c7, some c422, some c173, some c1164, some c359, some c813, some c174, some c9, some c72, some c1394, some c78, some c1015, some c282, some c16, some c42, some c326, some c328, some c63, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 57) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c1625, c1441, c1578, c1631, c379, c377, c569, c358, c66, c148, c7, c422, c173, c1164, c359, c813, c174, c9, c72, c1394, c78, c1015, c282, c16, c42, c326, c328, c63] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1631 := derived1631 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c569 := derived569 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c422 := derived422 a h
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c1164 := derived1164 a h
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c813 := derived813 a h
  have h16 : Entails.eval a c174 := h 173 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c72 := h 71 (by decide)
  have h19 : Entails.eval a c1394 := derived1394 a h
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c1015 := derived1015 a h
  have h22 : Entails.eval a c282 := h 281 (by decide)
  have h23 : Entails.eval a c16 := h 15 (by decide)
  have h24 : Entails.eval a c42 := h 41 (by decide)
  have h25 : Entails.eval a c326 := h 325 (by decide)
  have h26 : Entails.eval a c328 := h 327 (by decide)
  have h27 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1632, some c68, some c88, some c1164, some c379, some c377, some c569, some c359, some c358, some c66, some c148, some c813, some c92, some c9, some c154, some c375, some c78, some c279, some c38, some c323, some c633, some c54, some c330, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 57) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c1441, c1578, c1625, c1632, c68, c88, c1164, c379, c377, c569, c359, c358, c66, c148, c813, c92, c9, c154, c375, c78, c279, c38, c323, c633, c54, c330] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c1164 := derived1164 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c569 := derived569 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c154 := h 153 (by decide)
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c78 := h 77 (by decide)
  have h20 : Entails.eval a c279 := h 278 (by decide)
  have h21 : Entails.eval a c38 := h 37 (by decide)
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c633 := derived633 a h
  have h24 : Entails.eval a c54 := h 53 (by decide)
  have h25 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨51, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c659, some c37, some c330, some c339, some c55, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 57) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c1441, c659, c37, c330, c339, c55] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c330 := h 329 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1633, some c104, some c88, some c377, some c66, some c102, some c92, some c1634, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 57) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1578, c1625, c1441, c1633, c104, c88, c377, c66, c102, c92, c1634] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1633 := derived1633 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c1634 := derived1634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1636 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1635, some c66, some c672, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 57) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c1625, c1635, c66, c672] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c672 := derived672 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1635, some c90, some c88, some c1636, some c101, some c89, some c1403, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 57) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c1578, c1441, c1635, c90, c88, c1636, c101, c89, c1403] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c1636 := derived1636 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c1403 := derived1403 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1441, some c1635, some c1637, some c377, some c66, some c148, some c422, some c1060, some c1596, some c358, some c101, some c7, some c1164, some c174, some c79, some c9, some c1394, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 57) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c1625, c1578, c1441, c1635, c1637, c377, c66, c148, c422, c1060, c1596, c358, c101, c7, c1164, c174, c79, c9, c1394] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1637 := derived1637 a h
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c422 := derived422 a h
  have h9 : Entails.eval a c1060 := derived1060 a h
  have h10 : Entails.eval a c1596 := derived1596 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c1164 := derived1164 a h
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c1394 := derived1394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1635, some c1596, some c1637, some c377, some c66, some c148, some c358, some c422, some c1060, some c1638, some c92, some c9, some c102, some c154, some c1164, some c375, some c79, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 57) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1441, c1578, c1625, c1635, c1596, c1637, c377, c66, c148, c358, c422, c1060, c1638, c92, c9, c102, c154, c1164, c375, c79] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1596 := derived1596 a h
  have h5 : Entails.eval a c1637 := derived1637 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c422 := derived422 a h
  have h11 : Entails.eval a c1060 := derived1060 a h
  have h12 : Entails.eval a c1638 := derived1638 a h
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c1164 := derived1164 a h
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c66, some c292, some c36, some c336, some c54, some c59, some c346, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 57) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c1625, c1441, c66, c292, c36, c336, c54, c59, c346] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c292 := h 291 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c436, some c9, some c167, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 57) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1578, c436, c9, c167] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c88, some c1522, some c1379, some c185, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 57) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c1441, c1578, c88, c1522, c1379, c185] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c1522 := derived1522 a h
  have h4 : Entails.eval a c1379 := derived1379 a h
  have h5 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1639, some c65, some c633, some c54, some c313, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 57) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c1639, c65, c633, c54, c313] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c1639 := derived1639 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c633 := derived633 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c669, some c88, some c104, some c1639, some c65, some c67, some c450, some c1640, some c369, some c85, some c1641, some c148, some c157, some c292, some c1642, some c298, some c1643, some c336, some c342, some c260, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 57) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c1441, c1578, c1625, c669, c88, c104, c1639, c65, c67, c450, c1640, c369, c85, c1641, c148, c157, c292, c1642, c298, c1643, c336, c342, c260] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c669 := derived669 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c1639 := derived1639 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c450 := derived450 a h
  have h10 : Entails.eval a c1640 := derived1640 a h
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c1641 := derived1641 a h
  have h14 : Entails.eval a c148 := h 147 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c1642 := derived1642 a h
  have h18 : Entails.eval a c298 := h 297 (by decide)
  have h19 : Entails.eval a c1643 := derived1643 a h
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c342 := h 341 (by decide)
  have h22 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1639, some c65, some c67, some c88, some c669, some c104, some c450, some c1640, some c1644, some c813, some c384, some c1178, some c1185, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 57) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c1441, c1578, c1639, c65, c67, c88, c669, c104, c450, c1640, c1644, c813, c384, c1178, c1185] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c669 := derived669 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c450 := derived450 a h
  have h9 : Entails.eval a c1640 := derived1640 a h
  have h10 : Entails.eval a c1644 := derived1644 a h
  have h11 : Entails.eval a c813 := derived813 a h
  have h12 : Entails.eval a c384 := h 383 (by decide)
  have h13 : Entails.eval a c1178 := derived1178 a h
  have h14 : Entails.eval a c1185 := derived1185 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c66, some c1645, some c1639, some c543, some c104, some c1640, some c39, some c48, some c336, some c290, some c36, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 57) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c1625, c1441, c66, c1645, c1639, c543, c104, c1640, c39, c48, c336, c290, c36] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1639 := derived1639 a h
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c1640 := derived1640 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c336 := h 335 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c66, some c1639, some c84, some c1640, some c39, some c48, some c336, some c290, some c36, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 57) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1625, c1441, c66, c1639, c84, c1640, c39, c48, c336, c290, c36] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c1640 := derived1640 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1639, some c65, some c594, some c334, some c35, some c37, some c269, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 57) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1441, c1639, c65, c594, c334, c35, c37, c269] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1441, some c68, some c66, some c1639, some c65, some c1648, some c36, some c290, some c37, some c47, some c313, some c270, some c35, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 57) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c1625, c1578, c1441, c68, c66, c1639, c65, c1648, c36, c290, c37, c47, c313, c270, c35] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1648 := derived1648 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨54, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c243, some c107, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 57) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c239, c243, c107] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨32, by decide⟩, true), (⟨45, by decide⟩, false), (⟨28, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c231, some c228, some c203, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 57) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c231, c228, c203] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c231 := h 230 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨14, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c206, some c211, some c252, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 57) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c114, c206, c211, c252] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1653 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨21, by decide⟩, false), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c282, some c1651, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 57) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c282, c1651] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c282 := h 281 (by decide)
  have h1 : Entails.eval a c1651 := derived1651 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1654 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1639, some c65, some c1646, some c68, some c66, some c292, some c36, some c594, some c35, some c270, some c1645, some c382, some c85, some c1647, some c370, some c153, some c14, some c334, some c336, some c37, some c304, some c45, some c1539, some c1652, some c32, some c1649, some c366, some c1653, some c160, some c125, some c203, some c157, some c241, some c107, some c220, some c207, some c328, some c1104, some c198, some c119, some c58, some c1650, some c212, some c143, some c411, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 57) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1578, c1625, c1441, c1639, c65, c1646, c68, c66, c292, c36, c594, c35, c270, c1645, c382, c85, c1647, c370, c153, c14, c334, c336, c37, c304, c45, c1539, c1652, c32, c1649, c366, c1653, c160, c125, c203, c157, c241, c107, c220, c207, c328, c1104, c198, c119, c58, c1650, c212, c143, c411] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1646 := derived1646 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c594 := derived594 a h
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c1645 := derived1645 a h
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c1647 := derived1647 a h
  have h17 : Entails.eval a c370 := h 369 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c334 := h 333 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  have h22 : Entails.eval a c37 := h 36 (by decide)
  have h23 : Entails.eval a c304 := h 303 (by decide)
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c1539 := derived1539 a h
  have h26 : Entails.eval a c1652 := derived1652 a h
  have h27 : Entails.eval a c32 := h 31 (by decide)
  have h28 : Entails.eval a c1649 := derived1649 a h
  have h29 : Entails.eval a c366 := h 365 (by decide)
  have h30 : Entails.eval a c1653 := derived1653 a h
  have h31 : Entails.eval a c160 := h 159 (by decide)
  have h32 : Entails.eval a c125 := h 124 (by decide)
  have h33 : Entails.eval a c203 := h 202 (by decide)
  have h34 : Entails.eval a c157 := h 156 (by decide)
  have h35 : Entails.eval a c241 := h 240 (by decide)
  have h36 : Entails.eval a c107 := h 106 (by decide)
  have h37 : Entails.eval a c220 := h 219 (by decide)
  have h38 : Entails.eval a c207 := h 206 (by decide)
  have h39 : Entails.eval a c328 := h 327 (by decide)
  have h40 : Entails.eval a c1104 := derived1104 a h
  have h41 : Entails.eval a c198 := h 197 (by decide)
  have h42 : Entails.eval a c119 := h 118 (by decide)
  have h43 : Entails.eval a c58 := h 57 (by decide)
  have h44 : Entails.eval a c1650 := derived1650 a h
  have h45 : Entails.eval a c212 := h 211 (by decide)
  have h46 : Entails.eval a c143 := h 142 (by decide)
  have h47 : Entails.eval a c411 := h 410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1645, some c1646, some c1649, some c1647, some c1639, some c65, some c68, some c370, some c153, some c14, some c66, some c382, some c366, some c292, some c36, some c594, some c35, some c270, some c334, some c336, some c85, some c37, some c304, some c45, some c1539, some c1652, some c1653, some c160, some c157, some c32, some c241, some c107, some c220, some c207, some c328, some c1104, some c198, some c119, some c58, some c125, some c203, some c1654, some c1609, some c143, some c212, some c412, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 57) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1578, c1625, c1441, c1645, c1646, c1649, c1647, c1639, c65, c68, c370, c153, c14, c66, c382, c366, c292, c36, c594, c35, c270, c334, c336, c85, c37, c304, c45, c1539, c1652, c1653, c160, c157, c32, c241, c107, c220, c207, c328, c1104, c198, c119, c58, c125, c203, c1654, c1609, c143, c212, c412] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1646 := derived1646 a h
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c1647 := derived1647 a h
  have h7 : Entails.eval a c1639 := derived1639 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c366 := h 365 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c594 := derived594 a h
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c334 := h 333 (by decide)
  have h22 : Entails.eval a c336 := h 335 (by decide)
  have h23 : Entails.eval a c85 := h 84 (by decide)
  have h24 : Entails.eval a c37 := h 36 (by decide)
  have h25 : Entails.eval a c304 := h 303 (by decide)
  have h26 : Entails.eval a c45 := h 44 (by decide)
  have h27 : Entails.eval a c1539 := derived1539 a h
  have h28 : Entails.eval a c1652 := derived1652 a h
  have h29 : Entails.eval a c1653 := derived1653 a h
  have h30 : Entails.eval a c160 := h 159 (by decide)
  have h31 : Entails.eval a c157 := h 156 (by decide)
  have h32 : Entails.eval a c32 := h 31 (by decide)
  have h33 : Entails.eval a c241 := h 240 (by decide)
  have h34 : Entails.eval a c107 := h 106 (by decide)
  have h35 : Entails.eval a c220 := h 219 (by decide)
  have h36 : Entails.eval a c207 := h 206 (by decide)
  have h37 : Entails.eval a c328 := h 327 (by decide)
  have h38 : Entails.eval a c1104 := derived1104 a h
  have h39 : Entails.eval a c198 := h 197 (by decide)
  have h40 : Entails.eval a c119 := h 118 (by decide)
  have h41 : Entails.eval a c58 := h 57 (by decide)
  have h42 : Entails.eval a c125 := h 124 (by decide)
  have h43 : Entails.eval a c203 := h 202 (by decide)
  have h44 : Entails.eval a c1654 := derived1654 a h
  have h45 : Entails.eval a c1609 := derived1609 a h
  have h46 : Entails.eval a c143 := h 142 (by decide)
  have h47 : Entails.eval a c212 := h 211 (by decide)
  have h48 : Entails.eval a c412 := h 411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c1645, some c1647, some c1639, some c65, some c1646, some c68, some c370, some c153, some c14, some c66, some c382, some c85, some c292, some c36, some c594, some c334, some c336, some c35, some c37, some c304, some c45, some c1539, some c1104, some c157, some c1652, some c241, some c32, some c107, some c198, some c220, some c119, some c1655, some c106, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 57) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1578, c1441, c1625, c1645, c1647, c1639, c65, c1646, c68, c370, c153, c14, c66, c382, c85, c292, c36, c594, c334, c336, c35, c37, c304, c45, c1539, c1104, c157, c1652, c241, c32, c107, c198, c220, c119, c1655, c106] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1647 := derived1647 a h
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1646 := derived1646 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c594 := derived594 a h
  have h18 : Entails.eval a c334 := h 333 (by decide)
  have h19 : Entails.eval a c336 := h 335 (by decide)
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c37 := h 36 (by decide)
  have h22 : Entails.eval a c304 := h 303 (by decide)
  have h23 : Entails.eval a c45 := h 44 (by decide)
  have h24 : Entails.eval a c1539 := derived1539 a h
  have h25 : Entails.eval a c1104 := derived1104 a h
  have h26 : Entails.eval a c157 := h 156 (by decide)
  have h27 : Entails.eval a c1652 := derived1652 a h
  have h28 : Entails.eval a c241 := h 240 (by decide)
  have h29 : Entails.eval a c32 := h 31 (by decide)
  have h30 : Entails.eval a c107 := h 106 (by decide)
  have h31 : Entails.eval a c198 := h 197 (by decide)
  have h32 : Entails.eval a c220 := h 219 (by decide)
  have h33 : Entails.eval a c119 := h 118 (by decide)
  have h34 : Entails.eval a c1655 := derived1655 a h
  have h35 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c66, some c382, some c1639, some c65, some c68, some c370, some c366, some c1647, some c85, some c594, some c334, some c336, some c35, some c37, some c191, some c290, some c304, some c241, some c32, some c45, some c266, some c593, some c1539, some c157, some c328, some c220, some c207, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 57) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1578, c1441, c1625, c66, c382, c1639, c65, c68, c370, c366, c1647, c85, c594, c334, c336, c35, c37, c191, c290, c304, c241, c32, c45, c266, c593, c1539, c157, c328, c220, c207] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c1647 := derived1647 a h
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c594 := derived594 a h
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c304 := h 303 (by decide)
  have h20 : Entails.eval a c241 := h 240 (by decide)
  have h21 : Entails.eval a c32 := h 31 (by decide)
  have h22 : Entails.eval a c45 := h 44 (by decide)
  have h23 : Entails.eval a c266 := h 265 (by decide)
  have h24 : Entails.eval a c593 := derived593 a h
  have h25 : Entails.eval a c1539 := derived1539 a h
  have h26 : Entails.eval a c157 := h 156 (by decide)
  have h27 : Entails.eval a c328 := h 327 (by decide)
  have h28 : Entails.eval a c220 := h 219 (by decide)
  have h29 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, true), (⟨25, by decide⟩, true), (⟨34, by decide⟩, true), (⟨29, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c266, some c241, some c32, some c284, some c208, some c196, some c220, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 57) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c191, c266, c241, c32, c284, c208, c196, c220] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 57 := directClause ((⟨19, by decide⟩, true) :: (⟨31, by decide⟩, false) :: (⟨1, by decide⟩, true) :: (⟨2, by decide⟩, true) :: (⟨4, by decide⟩, true) :: (⟨7, by decide⟩, false) :: (⟨5, by decide⟩, false) :: (⟨6, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨35, by decide⟩, false) :: (⟨37, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨14, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨9, by decide⟩, true) :: (⟨17, by decide⟩, true) :: (⟨16, by decide⟩, false) :: (⟨11, by decide⟩, false) :: (⟨10, by decide⟩, true) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, false) :: (⟨23, by decide⟩, true) :: (⟨24, by decide⟩, true) :: (⟨25, by decide⟩, true) :: (⟨26, by decide⟩, false) :: (⟨20, by decide⟩, false) :: (⟨18, by decide⟩, true) :: (⟨29, by decide⟩, true) :: (⟨28, by decide⟩, false) :: (⟨56, by decide⟩, true) :: (⟨30, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨32, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨27, by decide⟩, true) :: (⟨36, by decide⟩, true) :: (⟨38, by decide⟩, true) :: (⟨39, by decide⟩, false) :: (⟨40, by decide⟩, true) :: (⟨41, by decide⟩, false) :: (⟨43, by decide⟩, true) :: (⟨44, by decide⟩, false) :: (⟨45, by decide⟩, true) :: (⟨46, by decide⟩, false) :: (⟨47, by decide⟩, true) :: (⟨48, by decide⟩, false) :: (⟨49, by decide⟩, true) :: (⟨50, by decide⟩, false) :: (⟨51, by decide⟩, false) :: (⟨53, by decide⟩, false) :: (⟨54, by decide⟩, false) :: (⟨55, by decide⟩, true) :: []) (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1625, some c1578, some c413, some c127, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 57) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1441, c1625, c1578, c413, c127] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c413 := h 412 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1639, some c1645, some c66, some c382, some c85, some c1647, some c32, some c65, some c1646, some c68, some c1656, some c1657, some c36, some c290, some c47, some c270, some c35, some c314, some c370, some c153, some c37, some c348, some c56, some c1104, some c241, some c209, some c135, some c167, some c1649, some c14, some c160, some c141, some c214, some c1539, some c157, some c366, some c208, some c220, some c196, some c284, some c1658, some c1650, some c201, some c1659, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 57) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c1441, c1578, c1625, c1639, c1645, c66, c382, c85, c1647, c32, c65, c1646, c68, c1656, c1657, c36, c290, c47, c270, c35, c314, c370, c153, c37, c348, c56, c1104, c241, c209, c135, c167, c1649, c14, c160, c141, c214, c1539, c157, c366, c208, c220, c196, c284, c1658, c1650, c201, c1659] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1647 := derived1647 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c1646 := derived1646 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c1656 := derived1656 a h
  have h14 : Entails.eval a c1657 := derived1657 a h
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c290 := h 289 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c314 := h 313 (by decide)
  have h21 : Entails.eval a c370 := h 369 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  have h23 : Entails.eval a c37 := h 36 (by decide)
  have h24 : Entails.eval a c348 := h 347 (by decide)
  have h25 : Entails.eval a c56 := h 55 (by decide)
  have h26 : Entails.eval a c1104 := derived1104 a h
  have h27 : Entails.eval a c241 := h 240 (by decide)
  have h28 : Entails.eval a c209 := h 208 (by decide)
  have h29 : Entails.eval a c135 := h 134 (by decide)
  have h30 : Entails.eval a c167 := h 166 (by decide)
  have h31 : Entails.eval a c1649 := derived1649 a h
  have h32 : Entails.eval a c14 := h 13 (by decide)
  have h33 : Entails.eval a c160 := h 159 (by decide)
  have h34 : Entails.eval a c141 := h 140 (by decide)
  have h35 : Entails.eval a c214 := h 213 (by decide)
  have h36 : Entails.eval a c1539 := derived1539 a h
  have h37 : Entails.eval a c157 := h 156 (by decide)
  have h38 : Entails.eval a c366 := h 365 (by decide)
  have h39 : Entails.eval a c208 := h 207 (by decide)
  have h40 : Entails.eval a c220 := h 219 (by decide)
  have h41 : Entails.eval a c196 := h 195 (by decide)
  have h42 : Entails.eval a c284 := h 283 (by decide)
  have h43 : Entails.eval a c1658 := derived1658 a h
  have h44 : Entails.eval a c1650 := derived1650 a h
  have h45 : Entails.eval a c201 := h 200 (by decide)
  have h46 : Entails.eval a c1659 := derived1659 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1639, some c1645, some c66, some c382, some c85, some c1646, some c1656, some c1657, some c36, some c290, some c37, some c65, some c68, some c47, some c270, some c35, some c348, some c56, some c1539, some c157, some c370, some c366, some c1647, some c32, some c241, some c208, some c220, some c196, some c284, some c153, some c1104, some c209, some c135, some c167, some c1658, some c314, some c14, some c1649, some c160, some c141, some c214, some c1660, some c1609, some c127, some c201, some c414, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 57) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c1578, c1625, c1441, c1639, c1645, c66, c382, c85, c1646, c1656, c1657, c36, c290, c37, c65, c68, c47, c270, c35, c348, c56, c1539, c157, c370, c366, c1647, c32, c241, c208, c220, c196, c284, c153, c1104, c209, c135, c167, c1658, c314, c14, c1649, c160, c141, c214, c1660, c1609, c127, c201, c414] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c1656 := derived1656 a h
  have h10 : Entails.eval a c1657 := derived1657 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c1539 := derived1539 a h
  have h22 : Entails.eval a c157 := h 156 (by decide)
  have h23 : Entails.eval a c370 := h 369 (by decide)
  have h24 : Entails.eval a c366 := h 365 (by decide)
  have h25 : Entails.eval a c1647 := derived1647 a h
  have h26 : Entails.eval a c32 := h 31 (by decide)
  have h27 : Entails.eval a c241 := h 240 (by decide)
  have h28 : Entails.eval a c208 := h 207 (by decide)
  have h29 : Entails.eval a c220 := h 219 (by decide)
  have h30 : Entails.eval a c196 := h 195 (by decide)
  have h31 : Entails.eval a c284 := h 283 (by decide)
  have h32 : Entails.eval a c153 := h 152 (by decide)
  have h33 : Entails.eval a c1104 := derived1104 a h
  have h34 : Entails.eval a c209 := h 208 (by decide)
  have h35 : Entails.eval a c135 := h 134 (by decide)
  have h36 : Entails.eval a c167 := h 166 (by decide)
  have h37 : Entails.eval a c1658 := derived1658 a h
  have h38 : Entails.eval a c314 := h 313 (by decide)
  have h39 : Entails.eval a c14 := h 13 (by decide)
  have h40 : Entails.eval a c1649 := derived1649 a h
  have h41 : Entails.eval a c160 := h 159 (by decide)
  have h42 : Entails.eval a c141 := h 140 (by decide)
  have h43 : Entails.eval a c214 := h 213 (by decide)
  have h44 : Entails.eval a c1660 := derived1660 a h
  have h45 : Entails.eval a c1609 := derived1609 a h
  have h46 : Entails.eval a c127 := h 126 (by decide)
  have h47 : Entails.eval a c201 := h 200 (by decide)
  have h48 : Entails.eval a c414 := h 413 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c1639, some c1645, some c66, some c382, some c85, some c1646, some c1656, some c1657, some c36, some c290, some c37, some c65, some c68, some c47, some c270, some c35, some c348, some c56, some c1539, some c157, some c314, some c370, some c366, some c1647, some c241, some c32, some c208, some c220, some c196, some c284, some c1661, some c228, some c1434, some c214, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 57) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c1578, c1441, c1625, c1639, c1645, c66, c382, c85, c1646, c1656, c1657, c36, c290, c37, c65, c68, c47, c270, c35, c348, c56, c1539, c157, c314, c370, c366, c1647, c241, c32, c208, c220, c196, c284, c1661, c228, c1434, c214] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c1656 := derived1656 a h
  have h10 : Entails.eval a c1657 := derived1657 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c1539 := derived1539 a h
  have h22 : Entails.eval a c157 := h 156 (by decide)
  have h23 : Entails.eval a c314 := h 313 (by decide)
  have h24 : Entails.eval a c370 := h 369 (by decide)
  have h25 : Entails.eval a c366 := h 365 (by decide)
  have h26 : Entails.eval a c1647 := derived1647 a h
  have h27 : Entails.eval a c241 := h 240 (by decide)
  have h28 : Entails.eval a c32 := h 31 (by decide)
  have h29 : Entails.eval a c208 := h 207 (by decide)
  have h30 : Entails.eval a c220 := h 219 (by decide)
  have h31 : Entails.eval a c196 := h 195 (by decide)
  have h32 : Entails.eval a c284 := h 283 (by decide)
  have h33 : Entails.eval a c1661 := derived1661 a h
  have h34 : Entails.eval a c228 := h 227 (by decide)
  have h35 : Entails.eval a c1434 := derived1434 a h
  have h36 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c1645, some c1647, some c1639, some c65, some c1646, some c68, some c370, some c153, some c14, some c66, some c382, some c85, some c1656, some c1657, some c36, some c290, some c37, some c47, some c270, some c35, some c348, some c56, some c1539, some c157, some c1662, some c114, some c195, some c220, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 57) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1578, c1441, c1625, c1645, c1647, c1639, c65, c1646, c68, c370, c153, c14, c66, c382, c85, c1656, c1657, c36, c290, c37, c47, c270, c35, c348, c56, c1539, c157, c1662, c114, c195, c220] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1647 := derived1647 a h
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c1646 := derived1646 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c1656 := derived1656 a h
  have h16 : Entails.eval a c1657 := derived1657 a h
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c348 := h 347 (by decide)
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c1539 := derived1539 a h
  have h26 : Entails.eval a c157 := h 156 (by decide)
  have h27 : Entails.eval a c1662 := derived1662 a h
  have h28 : Entails.eval a c114 := h 113 (by decide)
  have h29 : Entails.eval a c195 := h 194 (by decide)
  have h30 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c1578, some c1649, some c68, some c1639, some c66, some c382, some c85, some c594, some c334, some c336, some c35, some c37, some c58, some c290, some c304, some c137, some c45, some c174, some c1609, some c1539, some c182, some c1652, some c160, some c241, some c228, some c593, some c109, some c243, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 57) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1625, c1441, c1578, c1649, c68, c1639, c66, c382, c85, c594, c334, c336, c35, c37, c58, c290, c304, c137, c45, c174, c1609, c1539, c182, c1652, c160, c241, c228, c593, c109, c243] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1649 := derived1649 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c594 := derived594 a h
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c290 := h 289 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c174 := h 173 (by decide)
  have h20 : Entails.eval a c1609 := derived1609 a h
  have h21 : Entails.eval a c1539 := derived1539 a h
  have h22 : Entails.eval a c182 := h 181 (by decide)
  have h23 : Entails.eval a c1652 := derived1652 a h
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c241 := h 240 (by decide)
  have h26 : Entails.eval a c228 := h 227 (by decide)
  have h27 : Entails.eval a c593 := derived593 a h
  have h28 : Entails.eval a c109 := h 108 (by decide)
  have h29 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨54, by decide⟩, false), (⟨45, by decide⟩, false), (⟨11, by decide⟩, true), (⟨38, by decide⟩, true), (⟨12, by decide⟩, true), (⟨34, by decide⟩, true), (⟨53, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c228, some c208, some c109, some c243, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 57) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c241, c228, c208, c109, c243] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c1578, some c1645, some c1646, some c1649, some c1647, some c1639, some c65, some c68, some c370, some c66, some c382, some c85, some c153, some c14, some c1663, some c1664, some c36, some c292, some c290, some c37, some c47, some c270, some c121, some c35, some c174, some c348, some c182, some c56, some c160, some c1539, some c1609, some c1665, some c114, some c200, some c243, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 57) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1625, c1441, c1578, c1645, c1646, c1649, c1647, c1639, c65, c68, c370, c66, c382, c85, c153, c14, c1663, c1664, c36, c292, c290, c37, c47, c270, c121, c35, c174, c348, c182, c56, c160, c1539, c1609, c1665, c114, c200, c243] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1646 := derived1646 a h
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c1647 := derived1647 a h
  have h7 : Entails.eval a c1639 := derived1639 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c382 := h 381 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c1663 := derived1663 a h
  have h17 : Entails.eval a c1664 := derived1664 a h
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c290 := h 289 (by decide)
  have h21 : Entails.eval a c37 := h 36 (by decide)
  have h22 : Entails.eval a c47 := h 46 (by decide)
  have h23 : Entails.eval a c270 := h 269 (by decide)
  have h24 : Entails.eval a c121 := h 120 (by decide)
  have h25 : Entails.eval a c35 := h 34 (by decide)
  have h26 : Entails.eval a c174 := h 173 (by decide)
  have h27 : Entails.eval a c348 := h 347 (by decide)
  have h28 : Entails.eval a c182 := h 181 (by decide)
  have h29 : Entails.eval a c56 := h 55 (by decide)
  have h30 : Entails.eval a c160 := h 159 (by decide)
  have h31 : Entails.eval a c1539 := derived1539 a h
  have h32 : Entails.eval a c1609 := derived1609 a h
  have h33 : Entails.eval a c1665 := derived1665 a h
  have h34 : Entails.eval a c114 := h 113 (by decide)
  have h35 : Entails.eval a c200 := h 199 (by decide)
  have h36 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1667 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨35, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1650, some c1202, some c212, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 57) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1650, c1202, c212] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1650 := derived1650 a h
  have h1 : Entails.eval a c1202 := derived1202 a h
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1645, some c66, some c334, some c37, some c290, some c1646, some c594, some c35, some c304, some c45, some c1647, some c1639, some c65, some c68, some c370, some c158, some c1104, some c58, some c382, some c85, some c1666, some c16, some c14, some c336, some c1652, some c241, some c198, some c1667, some c1609, some c143, some c212, some c298, some c266, some c157, some c32, some c593, some c220, some c207, some c328, some c119, some c167, some c270, some c1649, some c160, some c125, some c203, some c415, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 57) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1578, c1625, c1441, c1645, c66, c334, c37, c290, c1646, c594, c35, c304, c45, c1647, c1639, c65, c68, c370, c158, c1104, c58, c382, c85, c1666, c16, c14, c336, c1652, c241, c198, c1667, c1609, c143, c212, c298, c266, c157, c32, c593, c220, c207, c328, c119, c167, c270, c1649, c160, c125, c203, c415] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c594 := derived594 a h
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c1647 := derived1647 a h
  have h14 : Entails.eval a c1639 := derived1639 a h
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c68 := h 67 (by decide)
  have h17 : Entails.eval a c370 := h 369 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c1104 := derived1104 a h
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c382 := h 381 (by decide)
  have h22 : Entails.eval a c85 := h 84 (by decide)
  have h23 : Entails.eval a c1666 := derived1666 a h
  have h24 : Entails.eval a c16 := h 15 (by decide)
  have h25 : Entails.eval a c14 := h 13 (by decide)
  have h26 : Entails.eval a c336 := h 335 (by decide)
  have h27 : Entails.eval a c1652 := derived1652 a h
  have h28 : Entails.eval a c241 := h 240 (by decide)
  have h29 : Entails.eval a c198 := h 197 (by decide)
  have h30 : Entails.eval a c1667 := derived1667 a h
  have h31 : Entails.eval a c1609 := derived1609 a h
  have h32 : Entails.eval a c143 := h 142 (by decide)
  have h33 : Entails.eval a c212 := h 211 (by decide)
  have h34 : Entails.eval a c298 := h 297 (by decide)
  have h35 : Entails.eval a c266 := h 265 (by decide)
  have h36 : Entails.eval a c157 := h 156 (by decide)
  have h37 : Entails.eval a c32 := h 31 (by decide)
  have h38 : Entails.eval a c593 := derived593 a h
  have h39 : Entails.eval a c220 := h 219 (by decide)
  have h40 : Entails.eval a c207 := h 206 (by decide)
  have h41 : Entails.eval a c328 := h 327 (by decide)
  have h42 : Entails.eval a c119 := h 118 (by decide)
  have h43 : Entails.eval a c167 := h 166 (by decide)
  have h44 : Entails.eval a c270 := h 269 (by decide)
  have h45 : Entails.eval a c1649 := derived1649 a h
  have h46 : Entails.eval a c160 := h 159 (by decide)
  have h47 : Entails.eval a c125 := h 124 (by decide)
  have h48 : Entails.eval a c203 := h 202 (by decide)
  have h49 : Entails.eval a c415 := h 414 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1645, some c66, some c334, some c37, some c290, some c1646, some c594, some c35, some c304, some c45, some c1639, some c65, some c68, some c270, some c58, some c336, some c1666, some c1649, some c1647, some c370, some c382, some c85, some c158, some c14, some c1104, some c16, some c157, some c1652, some c241, some c32, some c198, some c593, some c298, some c119, some c220, some c266, some c167, some c207, some c328, some c1667, some c1609, some c143, some c212, some c1668, some c228, some c203, some c125, some c416, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 57) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1578, c1625, c1441, c1645, c66, c334, c37, c290, c1646, c594, c35, c304, c45, c1639, c65, c68, c270, c58, c336, c1666, c1649, c1647, c370, c382, c85, c158, c14, c1104, c16, c157, c1652, c241, c32, c198, c593, c298, c119, c220, c266, c167, c207, c328, c1667, c1609, c143, c212, c1668, c228, c203, c125, c416] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c594 := derived594 a h
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c1639 := derived1639 a h
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c336 := h 335 (by decide)
  have h19 : Entails.eval a c1666 := derived1666 a h
  have h20 : Entails.eval a c1649 := derived1649 a h
  have h21 : Entails.eval a c1647 := derived1647 a h
  have h22 : Entails.eval a c370 := h 369 (by decide)
  have h23 : Entails.eval a c382 := h 381 (by decide)
  have h24 : Entails.eval a c85 := h 84 (by decide)
  have h25 : Entails.eval a c158 := h 157 (by decide)
  have h26 : Entails.eval a c14 := h 13 (by decide)
  have h27 : Entails.eval a c1104 := derived1104 a h
  have h28 : Entails.eval a c16 := h 15 (by decide)
  have h29 : Entails.eval a c157 := h 156 (by decide)
  have h30 : Entails.eval a c1652 := derived1652 a h
  have h31 : Entails.eval a c241 := h 240 (by decide)
  have h32 : Entails.eval a c32 := h 31 (by decide)
  have h33 : Entails.eval a c198 := h 197 (by decide)
  have h34 : Entails.eval a c593 := derived593 a h
  have h35 : Entails.eval a c298 := h 297 (by decide)
  have h36 : Entails.eval a c119 := h 118 (by decide)
  have h37 : Entails.eval a c220 := h 219 (by decide)
  have h38 : Entails.eval a c266 := h 265 (by decide)
  have h39 : Entails.eval a c167 := h 166 (by decide)
  have h40 : Entails.eval a c207 := h 206 (by decide)
  have h41 : Entails.eval a c328 := h 327 (by decide)
  have h42 : Entails.eval a c1667 := derived1667 a h
  have h43 : Entails.eval a c1609 := derived1609 a h
  have h44 : Entails.eval a c143 := h 142 (by decide)
  have h45 : Entails.eval a c212 := h 211 (by decide)
  have h46 : Entails.eval a c1668 := derived1668 a h
  have h47 : Entails.eval a c228 := h 227 (by decide)
  have h48 : Entails.eval a c203 := h 202 (by decide)
  have h49 : Entails.eval a c125 := h 124 (by decide)
  have h50 : Entails.eval a c416 := h 415 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1666, some c1645, some c1646, some c1649, some c1647, some c1639, some c65, some c68, some c370, some c66, some c382, some c85, some c594, some c334, some c336, some c35, some c37, some c58, some c290, some c304, some c45, some c1669, some c137, some c174, some c1609, some c184, some c1015, some c139, some c17, some c1104, some c1652, some c241, some c712, some c198, some c1202, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 57) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c1441, c1578, c1625, c1666, c1645, c1646, c1649, c1647, c1639, c65, c68, c370, c66, c382, c85, c594, c334, c336, c35, c37, c58, c290, c304, c45, c1669, c137, c174, c1609, c184, c1015, c139, c17, c1104, c1652, c241, c712, c198, c1202] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1666 := derived1666 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c1646 := derived1646 a h
  have h6 : Entails.eval a c1649 := derived1649 a h
  have h7 : Entails.eval a c1647 := derived1647 a h
  have h8 : Entails.eval a c1639 := derived1639 a h
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c594 := derived594 a h
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c290 := h 289 (by decide)
  have h22 : Entails.eval a c304 := h 303 (by decide)
  have h23 : Entails.eval a c45 := h 44 (by decide)
  have h24 : Entails.eval a c1669 := derived1669 a h
  have h25 : Entails.eval a c137 := h 136 (by decide)
  have h26 : Entails.eval a c174 := h 173 (by decide)
  have h27 : Entails.eval a c1609 := derived1609 a h
  have h28 : Entails.eval a c184 := h 183 (by decide)
  have h29 : Entails.eval a c1015 := derived1015 a h
  have h30 : Entails.eval a c139 := h 138 (by decide)
  have h31 : Entails.eval a c17 := h 16 (by decide)
  have h32 : Entails.eval a c1104 := derived1104 a h
  have h33 : Entails.eval a c1652 := derived1652 a h
  have h34 : Entails.eval a c241 := h 240 (by decide)
  have h35 : Entails.eval a c712 := derived712 a h
  have h36 : Entails.eval a c198 := h 197 (by decide)
  have h37 : Entails.eval a c1202 := derived1202 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨37, by decide⟩, true), (⟨14, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨38, by decide⟩, true), (⟨27, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1650, some c446, some c201, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 57) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1650, c446, c201] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1650 := derived1650 a h
  have h1 : Entails.eval a c446 := derived446 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1645, some c66, some c1670, some c36, some c290, some c37, some c1639, some c65, some c1646, some c68, some c47, some c270, some c35, some c348, some c56, some c1647, some c370, some c158, some c1104, some c382, some c85, some c1666, some c16, some c241, some c209, some c342, some c1671, some c1609, some c127, some c201, some c32, some c157, some c208, some c220, some c196, some c135, some c167, some c292, some c1658, some c266, some c14, some c314, some c1649, some c160, some c141, some c214, some c417, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 57) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1578, c1625, c1441, c1645, c66, c1670, c36, c290, c37, c1639, c65, c1646, c68, c47, c270, c35, c348, c56, c1647, c370, c158, c1104, c382, c85, c1666, c16, c241, c209, c342, c1671, c1609, c127, c201, c32, c157, c208, c220, c196, c135, c167, c292, c1658, c266, c14, c314, c1649, c160, c141, c214, c417] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1670 := derived1670 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c1639 := derived1639 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c1646 := derived1646 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c1647 := derived1647 a h
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c158 := h 157 (by decide)
  have h21 : Entails.eval a c1104 := derived1104 a h
  have h22 : Entails.eval a c382 := h 381 (by decide)
  have h23 : Entails.eval a c85 := h 84 (by decide)
  have h24 : Entails.eval a c1666 := derived1666 a h
  have h25 : Entails.eval a c16 := h 15 (by decide)
  have h26 : Entails.eval a c241 := h 240 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  have h28 : Entails.eval a c342 := h 341 (by decide)
  have h29 : Entails.eval a c1671 := derived1671 a h
  have h30 : Entails.eval a c1609 := derived1609 a h
  have h31 : Entails.eval a c127 := h 126 (by decide)
  have h32 : Entails.eval a c201 := h 200 (by decide)
  have h33 : Entails.eval a c32 := h 31 (by decide)
  have h34 : Entails.eval a c157 := h 156 (by decide)
  have h35 : Entails.eval a c208 := h 207 (by decide)
  have h36 : Entails.eval a c220 := h 219 (by decide)
  have h37 : Entails.eval a c196 := h 195 (by decide)
  have h38 : Entails.eval a c135 := h 134 (by decide)
  have h39 : Entails.eval a c167 := h 166 (by decide)
  have h40 : Entails.eval a c292 := h 291 (by decide)
  have h41 : Entails.eval a c1658 := derived1658 a h
  have h42 : Entails.eval a c266 := h 265 (by decide)
  have h43 : Entails.eval a c14 := h 13 (by decide)
  have h44 : Entails.eval a c314 := h 313 (by decide)
  have h45 : Entails.eval a c1649 := derived1649 a h
  have h46 : Entails.eval a c160 := h 159 (by decide)
  have h47 : Entails.eval a c141 := h 140 (by decide)
  have h48 : Entails.eval a c214 := h 213 (by decide)
  have h49 : Entails.eval a c417 := h 416 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1670, some c1645, some c66, some c36, some c290, some c37, some c1639, some c65, some c1646, some c68, some c47, some c270, some c35, some c348, some c56, some c370, some c158, some c16, some c157, some c1647, some c1104, some c14, some c314, some c292, some c1666, some c1649, some c382, some c85, some c241, some c32, some c209, some c208, some c342, some c135, some c220, some c266, some c1658, some c167, some c196, some c1671, some c1609, some c127, some c201, some c1672, some c228, some c214, some c141, some c418, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 57) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c1578, c1625, c1441, c1670, c1645, c66, c36, c290, c37, c1639, c65, c1646, c68, c47, c270, c35, c348, c56, c370, c158, c16, c157, c1647, c1104, c14, c314, c292, c1666, c1649, c382, c85, c241, c32, c209, c208, c342, c135, c220, c266, c1658, c167, c196, c1671, c1609, c127, c201, c1672, c228, c214, c141, c418] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1670 := derived1670 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c1639 := derived1639 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c1646 := derived1646 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c158 := h 157 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c157 := h 156 (by decide)
  have h22 : Entails.eval a c1647 := derived1647 a h
  have h23 : Entails.eval a c1104 := derived1104 a h
  have h24 : Entails.eval a c14 := h 13 (by decide)
  have h25 : Entails.eval a c314 := h 313 (by decide)
  have h26 : Entails.eval a c292 := h 291 (by decide)
  have h27 : Entails.eval a c1666 := derived1666 a h
  have h28 : Entails.eval a c1649 := derived1649 a h
  have h29 : Entails.eval a c382 := h 381 (by decide)
  have h30 : Entails.eval a c85 := h 84 (by decide)
  have h31 : Entails.eval a c241 := h 240 (by decide)
  have h32 : Entails.eval a c32 := h 31 (by decide)
  have h33 : Entails.eval a c209 := h 208 (by decide)
  have h34 : Entails.eval a c208 := h 207 (by decide)
  have h35 : Entails.eval a c342 := h 341 (by decide)
  have h36 : Entails.eval a c135 := h 134 (by decide)
  have h37 : Entails.eval a c220 := h 219 (by decide)
  have h38 : Entails.eval a c266 := h 265 (by decide)
  have h39 : Entails.eval a c1658 := derived1658 a h
  have h40 : Entails.eval a c167 := h 166 (by decide)
  have h41 : Entails.eval a c196 := h 195 (by decide)
  have h42 : Entails.eval a c1671 := derived1671 a h
  have h43 : Entails.eval a c1609 := derived1609 a h
  have h44 : Entails.eval a c127 := h 126 (by decide)
  have h45 : Entails.eval a c201 := h 200 (by decide)
  have h46 : Entails.eval a c1672 := derived1672 a h
  have h47 : Entails.eval a c228 := h 227 (by decide)
  have h48 : Entails.eval a c214 := h 213 (by decide)
  have h49 : Entails.eval a c141 := h 140 (by decide)
  have h50 : Entails.eval a c418 := h 417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1674 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c1670, some c1645, some c66, some c36, some c290, some c37, some c1639, some c65, some c1646, some c68, some c47, some c270, some c35, some c348, some c56, some c292, some c1647, some c370, some c158, some c14, some c16, some c157, some c1673, some c114, some c195, some c220, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1674 : lratChecker f1674 p1674 = .success := by decide +kernel
theorem unsat1674 : Unsatisfiable (PosFin 57) f1674 := by
  apply lratCheckerSound f1674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1674
  · intro a ha; simp [p1674] at ha; subst a; trivial
  · exact checked1674
theorem derived1674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1674 := by
  apply localUnsat_implies_entails f1674 [c1578, c1441, c1625, c1670, c1645, c66, c36, c290, c37, c1639, c65, c1646, c68, c47, c270, c35, c348, c56, c292, c1647, c370, c158, c14, c16, c157, c1673, c114, c195, c220] c1674 unsat1674 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1670 := derived1670 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c1639 := derived1639 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c1646 := derived1646 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c292 := h 291 (by decide)
  have h19 : Entails.eval a c1647 := derived1647 a h
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c158 := h 157 (by decide)
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c16 := h 15 (by decide)
  have h24 : Entails.eval a c157 := h 156 (by decide)
  have h25 : Entails.eval a c1673 := derived1673 a h
  have h26 : Entails.eval a c114 := h 113 (by decide)
  have h27 : Entails.eval a c195 := h 194 (by decide)
  have h28 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1675 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1441, some c1578, some c1645, some c1646, some c1649, some c68, some c1639, some c66, some c382, some c85, some c65, some c1670, some c36, some c292, some c290, some c37, some c47, some c270, some c35, some c348, some c56, some c1674, some c121, some c174, some c1609, some c182, some c184, some c17, some c160, some c1665, some c114, some c200, some c243, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1675 : lratChecker f1675 p1675 = .success := by decide +kernel
theorem unsat1675 : Unsatisfiable (PosFin 57) f1675 := by
  apply lratCheckerSound f1675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1675
  · intro a ha; simp [p1675] at ha; subst a; trivial
  · exact checked1675
theorem derived1675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1675 := by
  apply localUnsat_implies_entails f1675 [c1625, c1441, c1578, c1645, c1646, c1649, c68, c1639, c66, c382, c85, c65, c1670, c36, c292, c290, c37, c47, c270, c35, c348, c56, c1674, c121, c174, c1609, c182, c184, c17, c160, c1665, c114, c200, c243] c1675 unsat1675 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1646 := derived1646 a h
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c1639 := derived1639 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c1670 := derived1670 a h
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c290 := h 289 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c348 := h 347 (by decide)
  have h21 : Entails.eval a c56 := h 55 (by decide)
  have h22 : Entails.eval a c1674 := derived1674 a h
  have h23 : Entails.eval a c121 := h 120 (by decide)
  have h24 : Entails.eval a c174 := h 173 (by decide)
  have h25 : Entails.eval a c1609 := derived1609 a h
  have h26 : Entails.eval a c182 := h 181 (by decide)
  have h27 : Entails.eval a c184 := h 183 (by decide)
  have h28 : Entails.eval a c17 := h 16 (by decide)
  have h29 : Entails.eval a c160 := h 159 (by decide)
  have h30 : Entails.eval a c1665 := derived1665 a h
  have h31 : Entails.eval a c114 := h 113 (by decide)
  have h32 : Entails.eval a c200 := h 199 (by decide)
  have h33 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1676 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c109, some c228, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1676 : lratChecker f1676 p1676 = .success := by decide +kernel
theorem unsat1676 : Unsatisfiable (PosFin 57) f1676 := by
  apply lratCheckerSound f1676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1676
  · intro a ha; simp [p1676] at ha; subst a; trivial
  · exact checked1676
theorem derived1676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1676 := by
  apply localUnsat_implies_entails f1676 [c110, c109, c228] c1676 unsat1676 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1677 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c68, some c1639, some c65, some c37, some c58, some c116, some c314, some c35, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1677 : lratChecker f1677 p1677 = .success := by decide +kernel
theorem unsat1677 : Unsatisfiable (PosFin 57) f1677 := by
  apply lratCheckerSound f1677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1677
  · intro a ha; simp [p1677] at ha; subst a; trivial
  · exact checked1677
theorem derived1677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1677 := by
  apply localUnsat_implies_entails f1677 [c1578, c1441, c68, c1639, c65, c37, c58, c116, c314, c35] c1677 unsat1677 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1678 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1675, some c1645, some c1647, some c1639, some c65, some c1646, some c68, some c370, some c66, some c158, some c14, some c151, some c166, some c1608, some c180, some c181, some c1650, some c1676, some c1677, some c334, some c132, some c36, some c35, some c290, some c270, some c47, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1678 : lratChecker f1678 p1678 = .success := by decide +kernel
theorem unsat1678 : Unsatisfiable (PosFin 57) f1678 := by
  apply lratCheckerSound f1678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1678
  · intro a ha; simp [p1678] at ha; subst a; trivial
  · exact checked1678
theorem derived1678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1678 := by
  apply localUnsat_implies_entails f1678 [c1578, c1625, c1441, c1675, c1645, c1647, c1639, c65, c1646, c68, c370, c66, c158, c14, c151, c166, c1608, c180, c181, c1650, c1676, c1677, c334, c132, c36, c35, c290, c270, c47] c1678 unsat1678 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1675 := derived1675 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c1647 := derived1647 a h
  have h6 : Entails.eval a c1639 := derived1639 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c1608 := derived1608 a h
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c181 := h 180 (by decide)
  have h19 : Entails.eval a c1650 := derived1650 a h
  have h20 : Entails.eval a c1676 := derived1676 a h
  have h21 : Entails.eval a c1677 := derived1677 a h
  have h22 : Entails.eval a c334 := h 333 (by decide)
  have h23 : Entails.eval a c132 := h 131 (by decide)
  have h24 : Entails.eval a c36 := h 35 (by decide)
  have h25 : Entails.eval a c35 := h 34 (by decide)
  have h26 : Entails.eval a c290 := h 289 (by decide)
  have h27 : Entails.eval a c270 := h 269 (by decide)
  have h28 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1679 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1678, some c1675, some c1645, some c1646, some c1649, some c1647, some c1639, some c65, some c68, some c370, some c66, some c382, some c37, some c58, some c290, some c294, some c314, some c36, some c45, some c35, some c137, some c174, some c182, some c184, some c1015, some c160, some c1676, some c166, some c1104, some c239, some c119, some c198, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1679 : lratChecker f1679 p1679 = .success := by decide +kernel
theorem unsat1679 : Unsatisfiable (PosFin 57) f1679 := by
  apply lratCheckerSound f1679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1679
  · intro a ha; simp [p1679] at ha; subst a; trivial
  · exact checked1679
theorem derived1679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1679 := by
  apply localUnsat_implies_entails f1679 [c1441, c1578, c1625, c1678, c1675, c1645, c1646, c1649, c1647, c1639, c65, c68, c370, c66, c382, c37, c58, c290, c294, c314, c36, c45, c35, c137, c174, c182, c184, c1015, c160, c1676, c166, c1104, c239, c119, c198] c1679 unsat1679 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1678 := derived1678 a h
  have h4 : Entails.eval a c1675 := derived1675 a h
  have h5 : Entails.eval a c1645 := derived1645 a h
  have h6 : Entails.eval a c1646 := derived1646 a h
  have h7 : Entails.eval a c1649 := derived1649 a h
  have h8 : Entails.eval a c1647 := derived1647 a h
  have h9 : Entails.eval a c1639 := derived1639 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c290 := h 289 (by decide)
  have h18 : Entails.eval a c294 := h 293 (by decide)
  have h19 : Entails.eval a c314 := h 313 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c45 := h 44 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c137 := h 136 (by decide)
  have h24 : Entails.eval a c174 := h 173 (by decide)
  have h25 : Entails.eval a c182 := h 181 (by decide)
  have h26 : Entails.eval a c184 := h 183 (by decide)
  have h27 : Entails.eval a c1015 := derived1015 a h
  have h28 : Entails.eval a c160 := h 159 (by decide)
  have h29 : Entails.eval a c1676 := derived1676 a h
  have h30 : Entails.eval a c166 := h 165 (by decide)
  have h31 : Entails.eval a c1104 := derived1104 a h
  have h32 : Entails.eval a c239 := h 238 (by decide)
  have h33 : Entails.eval a c119 := h 118 (by decide)
  have h34 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1680 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1625, some c1678, some c1675, some c1645, some c1646, some c1649, some c1647, some c1639, some c65, some c68, some c370, some c66, some c382, some c1679, some c334, some c338, some c36, some c56, some c290, some c47, some c270, some c121, some c35, some c174, some c182, some c184, some c1015, some c160, some c1676, some c166, some c1104, some c239, some c135, some c209, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1680 : lratChecker f1680 p1680 = .success := by decide +kernel
theorem unsat1680 : Unsatisfiable (PosFin 57) f1680 := by
  apply lratCheckerSound f1680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1680
  · intro a ha; simp [p1680] at ha; subst a; trivial
  · exact checked1680
theorem derived1680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1680 := by
  apply localUnsat_implies_entails f1680 [c1441, c1578, c1625, c1678, c1675, c1645, c1646, c1649, c1647, c1639, c65, c68, c370, c66, c382, c1679, c334, c338, c36, c56, c290, c47, c270, c121, c35, c174, c182, c184, c1015, c160, c1676, c166, c1104, c239, c135, c209] c1680 unsat1680 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1678 := derived1678 a h
  have h4 : Entails.eval a c1675 := derived1675 a h
  have h5 : Entails.eval a c1645 := derived1645 a h
  have h6 : Entails.eval a c1646 := derived1646 a h
  have h7 : Entails.eval a c1649 := derived1649 a h
  have h8 : Entails.eval a c1647 := derived1647 a h
  have h9 : Entails.eval a c1639 := derived1639 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c1679 := derived1679 a h
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c338 := h 337 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c290 := h 289 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c270 := h 269 (by decide)
  have h23 : Entails.eval a c121 := h 120 (by decide)
  have h24 : Entails.eval a c35 := h 34 (by decide)
  have h25 : Entails.eval a c174 := h 173 (by decide)
  have h26 : Entails.eval a c182 := h 181 (by decide)
  have h27 : Entails.eval a c184 := h 183 (by decide)
  have h28 : Entails.eval a c1015 := derived1015 a h
  have h29 : Entails.eval a c160 := h 159 (by decide)
  have h30 : Entails.eval a c1676 := derived1676 a h
  have h31 : Entails.eval a c166 := h 165 (by decide)
  have h32 : Entails.eval a c1104 := derived1104 a h
  have h33 : Entails.eval a c239 := h 238 (by decide)
  have h34 : Entails.eval a c135 := h 134 (by decide)
  have h35 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1681 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1645, some c1639, some c65, some c66, some c382, some c85, some c1646, some c68, some c370, some c1675, some c1678, some c1680, some c91, some c603, some c1609, some c17, some c178, some c167, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c1578, c1625, c1645, c1639, c65, c66, c382, c85, c1646, c68, c370, c1675, c1678, c1680, c91, c603, c1609, c17, c178, c167] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1645 := derived1645 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c1675 := derived1675 a h
  have h12 : Entails.eval a c1678 := derived1678 a h
  have h13 : Entails.eval a c1680 := derived1680 a h
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c603 := derived603 a h
  have h16 : Entails.eval a c1609 := derived1609 a h
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c178 := h 177 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c68, some c1639, some c65, some c561, some c38, some c270, some c279, some c43, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1578, c68, c1639, c65, c561, c38, c270, c279, c43] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c561 := derived561 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1441, some c1639, some c65, some c68, some c370, some c158, some c1682, some c78, some c369, some c455, some c82, some c16, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c1578, c1625, c1441, c1639, c65, c68, c370, c158, c1682, c78, c369, c455, c82, c16] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c1682 := derived1682 a h
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c455 := derived455 a h
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1684 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨36, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨45, by decide⟩, false), (⟨46, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c270, some c271, some c190, some c264, some c219, some c228, some c24, some c315, some c338, some c206, some c37, some c336, some c290, some c188, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1441, c270, c271, c190, c264, c219, c228, c24, c315, c338, c206, c37, c336, c290, c188] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c338 := h 337 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1441, some c1681, some c1639, some c1645, some c382, some c85, some c102, some c1683, some c84, some c65, some c157, some c455, some c371, some c78, some c158, some c13, some c150, some c173, some c561, some c1684, some c35, some c43, some c315, some c292, some c279, some c264, some c190, some c294, some c24, some c37, some c188, some c334, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c1625, c1578, c1441, c1681, c1639, c1645, c382, c85, c102, c1683, c84, c65, c157, c455, c371, c78, c158, c13, c150, c173, c561, c1684, c35, c43, c315, c292, c279, c264, c190, c294, c24, c37, c188, c334] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1681 := derived1681 a h
  have h4 : Entails.eval a c1639 := derived1639 a h
  have h5 : Entails.eval a c1645 := derived1645 a h
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c1683 := derived1683 a h
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c157 := h 156 (by decide)
  have h13 : Entails.eval a c455 := derived455 a h
  have h14 : Entails.eval a c371 := h 370 (by decide)
  have h15 : Entails.eval a c78 := h 77 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c150 := h 149 (by decide)
  have h19 : Entails.eval a c173 := h 172 (by decide)
  have h20 : Entails.eval a c561 := derived561 a h
  have h21 : Entails.eval a c1684 := derived1684 a h
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c43 := h 42 (by decide)
  have h24 : Entails.eval a c315 := h 314 (by decide)
  have h25 : Entails.eval a c292 := h 291 (by decide)
  have h26 : Entails.eval a c279 := h 278 (by decide)
  have h27 : Entails.eval a c264 := h 263 (by decide)
  have h28 : Entails.eval a c190 := h 189 (by decide)
  have h29 : Entails.eval a c294 := h 293 (by decide)
  have h30 : Entails.eval a c24 := h 23 (by decide)
  have h31 : Entails.eval a c37 := h 36 (by decide)
  have h32 : Entails.eval a c188 := h 187 (by decide)
  have h33 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨25, by decide⟩, false), (⟨44, by decide⟩, false), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1441, some c1645, some c382, some c1681, some c1639, some c85, some c102, some c1683, some c65, some c370, some c158, some c13, some c174, some c1685, some c16, some c84, some c633, some c37, some c336, some c290, some c269, some c304, some c188, some c78, some c40, some c26, some c24, some c561, some c146, some c214, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c1625, c1578, c1441, c1645, c382, c1681, c1639, c85, c102, c1683, c65, c370, c158, c13, c174, c1685, c16, c84, c633, c37, c336, c290, c269, c304, c188, c78, c40, c26, c24, c561, c146, c214] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c1681 := derived1681 a h
  have h6 : Entails.eval a c1639 := derived1639 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c1683 := derived1683 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c1685 := derived1685 a h
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c633 := derived633 a h
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c290 := h 289 (by decide)
  have h22 : Entails.eval a c269 := h 268 (by decide)
  have h23 : Entails.eval a c304 := h 303 (by decide)
  have h24 : Entails.eval a c188 := h 187 (by decide)
  have h25 : Entails.eval a c78 := h 77 (by decide)
  have h26 : Entails.eval a c40 := h 39 (by decide)
  have h27 : Entails.eval a c26 := h 25 (by decide)
  have h28 : Entails.eval a c24 := h 23 (by decide)
  have h29 : Entails.eval a c561 := derived561 a h
  have h30 : Entails.eval a c146 := h 145 (by decide)
  have h31 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c78, some c82, some c369, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1441, c78, c82, c369] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨44, by decide⟩, false), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1639, some c65, some c1681, some c1645, some c382, some c85, some c102, some c1685, some c370, some c158, some c16, some c1687, some c561, some c181, some c1683, some c84, some c270, some c1686, some c334, some c190, some c219, some c228, some c24, some c30, some c105, some c188, some c209, some c292, some c144, some c39, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c1625, c1639, c65, c1681, c1645, c382, c85, c102, c1685, c370, c158, c16, c1687, c561, c181, c1683, c84, c270, c1686, c334, c190, c219, c228, c24, c30, c105, c188, c209, c292, c144, c39] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c1681 := derived1681 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c1685 := derived1685 a h
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c1687 := derived1687 a h
  have h13 : Entails.eval a c561 := derived561 a h
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c1683 := derived1683 a h
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c1686 := derived1686 a h
  have h19 : Entails.eval a c334 := h 333 (by decide)
  have h20 : Entails.eval a c190 := h 189 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  have h23 : Entails.eval a c24 := h 23 (by decide)
  have h24 : Entails.eval a c30 := h 29 (by decide)
  have h25 : Entails.eval a c105 := h 104 (by decide)
  have h26 : Entails.eval a c188 := h 187 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  have h28 : Entails.eval a c292 := h 291 (by decide)
  have h29 : Entails.eval a c144 := h 143 (by decide)
  have h30 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1689 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1685, some c1681, some c1639, some c1645, some c382, some c85, some c102, some c1683, some c84, some c65, some c370, some c158, some c16, some c181, some c1687, some c561, some c1688, some c43, some c292, some c279, some c190, some c219, some c228, some c24, some c30, some c105, some c198, some c128, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c1625, c1685, c1681, c1639, c1645, c382, c85, c102, c1683, c84, c65, c370, c158, c16, c181, c1687, c561, c1688, c43, c292, c279, c190, c219, c228, c24, c30, c105, c198, c128] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1685 := derived1685 a h
  have h2 : Entails.eval a c1681 := derived1681 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c1683 := derived1683 a h
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c1687 := derived1687 a h
  have h16 : Entails.eval a c561 := derived561 a h
  have h17 : Entails.eval a c1688 := derived1688 a h
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c279 := h 278 (by decide)
  have h21 : Entails.eval a c190 := h 189 (by decide)
  have h22 : Entails.eval a c219 := h 218 (by decide)
  have h23 : Entails.eval a c228 := h 227 (by decide)
  have h24 : Entails.eval a c24 := h 23 (by decide)
  have h25 : Entails.eval a c30 := h 29 (by decide)
  have h26 : Entails.eval a c105 := h 104 (by decide)
  have h27 : Entails.eval a c198 := h 197 (by decide)
  have h28 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨14, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1639, some c85, some c102, some c84, some c65, some c78, some c82, some c450, some c1643, some c1539, some c292, some c336, some c298, some c342, some c260, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c1441, c1639, c85, c102, c84, c65, c78, c82, c450, c1643, c1539, c292, c336, c298, c342, c260] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c450 := derived450 a h
  have h9 : Entails.eval a c1643 := derived1643 a h
  have h10 : Entails.eval a c1539 := derived1539 a h
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c334, some c336, some c633, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c334, c336, c633] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c334 := h 333 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1639, some c65, some c316, some c325, some c54, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1639, c65, c316, c325, c54] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1639 := derived1639 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1693 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c292, some c290, some c48, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1441, c292, c290, c48] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1694 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1645, some c1681, some c1639, some c382, some c85, some c102, some c84, some c1693, some c1691, some c65, some c1683, some c1685, some c1689, some c150, some c13, some c158, some c371, some c1690, some c1692, some c260, some c281, some c272, some c43, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c1578, c1625, c1645, c1681, c1639, c382, c85, c102, c84, c1693, c1691, c65, c1683, c1685, c1689, c150, c13, c158, c371, c1690, c1692, c260, c281, c272, c43] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1645 := derived1645 a h
  have h3 : Entails.eval a c1681 := derived1681 a h
  have h4 : Entails.eval a c1639 := derived1639 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c1693 := derived1693 a h
  have h10 : Entails.eval a c1691 := derived1691 a h
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c1683 := derived1683 a h
  have h13 : Entails.eval a c1685 := derived1685 a h
  have h14 : Entails.eval a c1689 := derived1689 a h
  have h15 : Entails.eval a c150 := h 149 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c158 := h 157 (by decide)
  have h18 : Entails.eval a c371 := h 370 (by decide)
  have h19 : Entails.eval a c1690 := derived1690 a h
  have h20 : Entails.eval a c1692 := derived1692 a h
  have h21 : Entails.eval a c260 := h 259 (by decide)
  have h22 : Entails.eval a c281 := h 280 (by decide)
  have h23 : Entails.eval a c272 := h 271 (by decide)
  have h24 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1681, some c1645, some c1639, some c382, some c85, some c1694, some c9, some c167, some c174, some c178, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1578, c1681, c1645, c1639, c382, c85, c1694, c9, c167, c174, c178] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1681 := derived1681 a h
  have h2 : Entails.eval a c1645 := derived1645 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c1694 := derived1694 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c174 := h 173 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1639, some c65, some c1681, some c1695, some c148, some c422, some c1185, some c813, some c85, some c9, some c167, some c174, some c178, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1625, c1578, c1639, c65, c1681, c1695, c148, c422, c1185, c813, c85, c9, c167, c174, c178] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c1681 := derived1681 a h
  have h5 : Entails.eval a c1695 := derived1695 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c422 := derived422 a h
  have h8 : Entails.eval a c1185 := derived1185 a h
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c174 := h 173 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1578, some c1696, some c1639, some c65, some c66, some c76, some c1067, some c1534, some c360, some c1557, some c1558, some c272, some c316, some c35, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c1625, c1578, c1696, c1639, c65, c66, c76, c1067, c1534, c360, c1557, c1558, c272, c316, c35] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c1067 := derived1067 a h
  have h8 : Entails.eval a c1534 := derived1534 a h
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c1557 := derived1557 a h
  have h11 : Entails.eval a c1558 := derived1558 a h
  have h12 : Entails.eval a c272 := h 271 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1639, some c84, some c1696, some c65, some c79, some c71, some c450, some c269, some c298, some c49, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c1441, c1639, c84, c1696, c65, c79, c71, c450, c269, c298, c49] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c450 := derived450 a h
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c102, some c1696, some c1639, some c65, some c1698, some c1534, some c272, some c1241, some c41, some c1692, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1697, c102, c1696, c1639, c65, c1698, c1534, c272, c1241, c41, c1692] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1698 := derived1698 a h
  have h6 : Entails.eval a c1534 := derived1534 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c1241 := derived1241 a h
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c1692 := derived1692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1699, some c35, some c1639, some c1697, some c102, some c84, some c1696, some c65, some c79, some c71, some c1643, some c313, some c342, some c60, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c1441, c1699, c35, c1639, c1697, c102, c84, c1696, c65, c79, c71, c1643, c313, c342, c60] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1699 := derived1699 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1697 := derived1697 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c1696 := derived1696 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c1643 := derived1643 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1696, some c1639, some c65, some c102, some c1699, some c35, some c43, some c1700, some c1534, some c316, some c1241, some c41, some c281, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1697, c1696, c1639, c65, c102, c1699, c35, c43, c1700, c1534, c316, c1241, c41, c281] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c1699 := derived1699 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c1700 := derived1700 a h
  have h9 : Entails.eval a c1534 := derived1534 a h
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c1241 := derived1241 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c65, some c1696, some c1701, some c85, some c813, some c1060, some c71, some c90, some c385, some c371, some c363, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c1578, c1441, c65, c1696, c1701, c85, c813, c1060, c71, c90, c385, c371, c363] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1701 := derived1701 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1639, some c1702, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1639, c1702] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1639 := derived1639 a h
  have h1 : Entails.eval a c1702 := derived1702 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1703, some c882, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c1703, c882] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c1703 := derived1703 a h
  have h1 : Entails.eval a c882 := derived882 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨22, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c114, some c241, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c107, c114, c241] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1625, some c1703, some c1704, some c1441, some c99, some c75, some c98, some c68, some c541, some c1025, some c187, some c220, some c370, some c88, some c91, some c379, some c971, some c66, some c1568, some c158, some c5, some c14, some c167, some c166, some c1705, some c185, some c160, some c279, some c257, some c336, some c323, some c56, some c58, some c338, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c1578, c1625, c1703, c1704, c1441, c99, c75, c98, c68, c541, c1025, c187, c220, c370, c88, c91, c379, c971, c66, c1568, c158, c5, c14, c167, c166, c1705, c185, c160, c279, c257, c336, c323, c56, c58, c338] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c1703 := derived1703 a h
  have h3 : Entails.eval a c1704 := derived1704 a h
  have h4 : Entails.eval a c1441 := derived1441 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c541 := derived541 a h
  have h10 : Entails.eval a c1025 := derived1025 a h
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c220 := h 219 (by decide)
  have h13 : Entails.eval a c370 := h 369 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c379 := h 378 (by decide)
  have h17 : Entails.eval a c971 := derived971 a h
  have h18 : Entails.eval a c66 := h 65 (by decide)
  have h19 : Entails.eval a c1568 := derived1568 a h
  have h20 : Entails.eval a c158 := h 157 (by decide)
  have h21 : Entails.eval a c5 := h 4 (by decide)
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c167 := h 166 (by decide)
  have h24 : Entails.eval a c166 := h 165 (by decide)
  have h25 : Entails.eval a c1705 := derived1705 a h
  have h26 : Entails.eval a c185 := h 184 (by decide)
  have h27 : Entails.eval a c160 := h 159 (by decide)
  have h28 : Entails.eval a c279 := h 278 (by decide)
  have h29 : Entails.eval a c257 := h 256 (by decide)
  have h30 : Entails.eval a c336 := h 335 (by decide)
  have h31 : Entails.eval a c323 := h 322 (by decide)
  have h32 : Entails.eval a c56 := h 55 (by decide)
  have h33 : Entails.eval a c58 := h 57 (by decide)
  have h34 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨45, by decide⟩, true), (⟨10, by decide⟩, false), (⟨47, by decide⟩, true), (⟨43, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1704, some c1230, some c178, some c182, some c167, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c1704, c1230, c178, c182, c167] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c1704 := derived1704 a h
  have h1 : Entails.eval a c1230 := derived1230 a h
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨10, by decide⟩, false), (⟨49, by decide⟩, true), (⟨47, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1704, some c1707, some c174, some c182, some c184, some c160, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c1578, c1704, c1707, c174, c182, c184, c160] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1704 := derived1704 a h
  have h2 : Entails.eval a c1707 := derived1707 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1703, some c1578, some c1441, some c98, some c99, some c91, some c88, some c58, some c338, some c213, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c1703, c1578, c1441, c98, c99, c91, c88, c58, c338, c213] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c1703 := derived1703 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c338 := h 337 (by decide)
  have h9 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1578, some c1703, some c98, some c99, some c91, some c88, some c1568, some c68, some c279, some c323, some c257, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c1441, c1578, c1703, c98, c99, c91, c88, c1568, c68, c279, c323, c257] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1703 := derived1703 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c1568 := derived1568 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c279 := h 278 (by decide)
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1703, some c1578, some c1704, some c1441, some c98, some c88, some c99, some c91, some c379, some c75, some c971, some c68, some c541, some c1025, some c370, some c187, some c219, some c220, some c1709, some c1710, some c78, some c1708, some c1706, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c1625, c1703, c1578, c1704, c1441, c98, c88, c99, c91, c379, c75, c971, c68, c541, c1025, c370, c187, c219, c220, c1709, c1710, c78, c1708, c1706] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1703 := derived1703 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1704 := derived1704 a h
  have h4 : Entails.eval a c1441 := derived1441 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c971 := derived971 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c541 := derived541 a h
  have h14 : Entails.eval a c1025 := derived1025 a h
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c1709 := derived1709 a h
  have h20 : Entails.eval a c1710 := derived1710 a h
  have h21 : Entails.eval a c78 := h 77 (by decide)
  have h22 : Entails.eval a c1708 := derived1708 a h
  have h23 : Entails.eval a c1706 := derived1706 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c158, some c161, some c177, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1625, c158, c161, c177] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c161 := h 160 (by decide)
  have h3 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1713 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, false), (⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1704, some c1578, some c174, some c112, some c15, some c1276, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1713 : lratChecker f1713 p1713 = .success := by decide +kernel
theorem unsat1713 : Unsatisfiable (PosFin 57) f1713 := by
  apply lratCheckerSound f1713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1713
  · intro a ha; simp [p1713] at ha; subst a; trivial
  · exact checked1713
theorem derived1713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1713 := by
  apply localUnsat_implies_entails f1713 [c1704, c1578, c174, c112, c15, c1276] c1713 unsat1713 (by rfl) a
  have h0 : Entails.eval a c1704 := derived1704 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c174 := h 173 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1276 := derived1276 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1714 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1578, some c1441, some c1625, some c1704, some c1703, some c98, some c88, some c99, some c91, some c379, some c1568, some c92, some c68, some c66, some c75, some c971, some c1711, some c147, some c5, some c1712, some c376, some c1225, some c280, some c980, some c193, some c22, some c229, some c232, some c1709, some c1713, some c117, some c133, some c187, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c1578, c1441, c1625, c1704, c1703, c98, c88, c99, c91, c379, c1568, c92, c68, c66, c75, c971, c1711, c147, c5, c1712, c376, c1225, c280, c980, c193, c22, c229, c232, c1709, c1713, c117, c133, c187] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c1578 := derived1578 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1704 := derived1704 a h
  have h4 : Entails.eval a c1703 := derived1703 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c379 := h 378 (by decide)
  have h10 : Entails.eval a c1568 := derived1568 a h
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c971 := derived971 a h
  have h16 : Entails.eval a c1711 := derived1711 a h
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c5 := h 4 (by decide)
  have h19 : Entails.eval a c1712 := derived1712 a h
  have h20 : Entails.eval a c376 := h 375 (by decide)
  have h21 : Entails.eval a c1225 := derived1225 a h
  have h22 : Entails.eval a c280 := h 279 (by decide)
  have h23 : Entails.eval a c980 := derived980 a h
  have h24 : Entails.eval a c193 := h 192 (by decide)
  have h25 : Entails.eval a c22 := h 21 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  have h27 : Entails.eval a c232 := h 231 (by decide)
  have h28 : Entails.eval a c1709 := derived1709 a h
  have h29 : Entails.eval a c1713 := derived1713 a h
  have h30 : Entails.eval a c117 := h 116 (by decide)
  have h31 : Entails.eval a c133 := h 132 (by decide)
  have h32 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1703, some c1704, some c1578, some c1441, some c98, some c92, some c1714, some c102, some c99, some c91, some c88, some c48, some c52, some c294, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c1703, c1704, c1578, c1441, c98, c92, c1714, c102, c99, c91, c88, c48, c52, c294] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c1703 := derived1703 a h
  have h1 : Entails.eval a c1704 := derived1704 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c1714 := derived1714 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1703, some c1578, some c1441, some c1704, some c98, some c99, some c68, some c88, some c92, some c91, some c1568, some c379, some c1714, some c102, some c1715, some c279, some c78, some c82, some c971, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c1703, c1578, c1441, c1704, c98, c99, c68, c88, c92, c91, c1568, c379, c1714, c102, c1715, c279, c78, c82, c971] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c1703 := derived1703 a h
  have h1 : Entails.eval a c1578 := derived1578 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1704 := derived1704 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c1568 := derived1568 a h
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c1714 := derived1714 a h
  have h13 : Entails.eval a c102 := h 101 (by decide)
  have h14 : Entails.eval a c1715 := derived1715 a h
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c78 := h 77 (by decide)
  have h17 : Entails.eval a c82 := h 81 (by decide)
  have h18 : Entails.eval a c971 := derived971 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨13, by decide⟩, true), (⟨2, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1625, some c1703, some c1578, some c1716, some c1704, some c1067, some c68, some c150, some c3, some c76, some c371, some c363, some c1596, some c166, some c1334, some c66, some c1557, some c1558, some c1202, some c316, some c94, some c1539, some c164, some c325, some c746, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c1625, c1703, c1578, c1716, c1704, c1067, c68, c150, c3, c76, c371, c363, c1596, c166, c1334, c66, c1557, c1558, c1202, c316, c94, c1539, c164, c325, c746] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c1625 := derived1625 a h
  have h1 : Entails.eval a c1703 := derived1703 a h
  have h2 : Entails.eval a c1578 := derived1578 a h
  have h3 : Entails.eval a c1716 := derived1716 a h
  have h4 : Entails.eval a c1704 := derived1704 a h
  have h5 : Entails.eval a c1067 := derived1067 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c371 := h 370 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c1596 := derived1596 a h
  have h13 : Entails.eval a c166 := h 165 (by decide)
  have h14 : Entails.eval a c1334 := derived1334 a h
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c1557 := derived1557 a h
  have h17 : Entails.eval a c1558 := derived1558 a h
  have h18 : Entails.eval a c1202 := derived1202 a h
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c94 := h 93 (by decide)
  have h21 : Entails.eval a c1539 := derived1539 a h
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c325 := h 324 (by decide)
  have h24 : Entails.eval a c746 := derived746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1441, some c1716, some c747, some c1572, some c1202, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c1441, c1716, c747, c1572, c1202] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1716 := derived1716 a h
  have h2 : Entails.eval a c747 := derived747 a h
  have h3 : Entails.eval a c1572 := derived1572 a h
  have h4 : Entails.eval a c1202 := derived1202 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1718

end CochromaticTwenty.Certificates.B16_8_0Enumerating
