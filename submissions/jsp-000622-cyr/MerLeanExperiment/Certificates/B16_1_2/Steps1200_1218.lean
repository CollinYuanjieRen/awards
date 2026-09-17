import MerLeanExperiment.Certificates.B16_1_2.Steps1100_1199

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1594 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨14, by decide⟩, false), (⟨35, by decide⟩, true), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1585, some c1432, some c1574, some c29, some c59, some c127, some c126, some c324, some c52, some c222, some c143, some c133, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 57) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c1431, c1585, c1432, c1574, c29, c59, c127, c126, c324, c52, c222, c143, c133] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1432 := derived1432 a h
  have h3 : Entails.eval a c1574 := derived1574 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1432, some c1586, some c1585, some c1589, some c1588, some c1574, some c122, some c1591, some c1593, some c498, some c5, some c145, some c1449, some c123, some c78, some c158, some c205, some c10, some c2, some c1594, some c323, some c35, some c64, some c561, some c310, some c386, some c112, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 57) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c1432, c1586, c1585, c1589, c1588, c1574, c122, c1591, c1593, c498, c5, c145, c1449, c123, c78, c158, c205, c10, c2, c1594, c323, c35, c64, c561, c310, c386, c112] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c1432 := derived1432 a h
  have h1 : Entails.eval a c1586 := derived1586 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1589 := derived1589 a h
  have h4 : Entails.eval a c1588 := derived1588 a h
  have h5 : Entails.eval a c1574 := derived1574 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c1591 := derived1591 a h
  have h8 : Entails.eval a c1593 := derived1593 a h
  have h9 : Entails.eval a c498 := derived498 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c1449 := derived1449 a h
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c1594 := derived1594 a h
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c35 := h 34 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c561 := derived561 a h
  have h24 : Entails.eval a c310 := h 309 (by decide)
  have h25 : Entails.eval a c386 := h 385 (by decide)
  have h26 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1585, some c1432, some c1431, some c127, some c43, some c56, some c175, some c126, some c85, some c14, some c254, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 57) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c1574, c1585, c1432, c1431, c127, c43, c56, c175, c126, c85, c14, c254] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1432 := derived1432 a h
  have h3 : Entails.eval a c1431 := derived1431 a h
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1431, some c1585, some c1574, some c1432, some c1596, some c37, some c29, some c175, some c104, some c174, some c290, some c6, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 57) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c1431, c1585, c1574, c1432, c1596, c37, c29, c175, c104, c174, c290, c6] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c1431 := derived1431 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c1432 := derived1432 a h
  have h4 : Entails.eval a c1596 := derived1596 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c174 := h 173 (by decide)
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1597, some c1589, some c122, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 57) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1597, c1589, c122] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1597 := derived1597 a h
  have h1 : Entails.eval a c1589 := derived1589 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1597, some c1595, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 57) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1597, c1595] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1597 := derived1597 a h
  have h1 : Entails.eval a c1595 := derived1595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1600 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1574, some c1432, some c1585, some c1599, some c1431, some c29, some c58, some c127, some c35, some c43, some c175, some c299, some c94, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 57) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1574, c1432, c1585, c1599, c1431, c29, c58, c127, c35, c43, c175, c299, c94] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1574 := derived1574 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1599 := derived1599 a h
  have h4 : Entails.eval a c1431 := derived1431 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1588, some c1600, some c1574, some c1599, some c1585, some c1259, some c1590, some c392, some c323, some c11, some c35, some c1519, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 57) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1587, c1588, c1600, c1574, c1599, c1585, c1259, c1590, c392, c323, c11, c35, c1519] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1588 := derived1588 a h
  have h2 : Entails.eval a c1600 := derived1600 a h
  have h3 : Entails.eval a c1574 := derived1574 a h
  have h4 : Entails.eval a c1599 := derived1599 a h
  have h5 : Entails.eval a c1585 := derived1585 a h
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c1590 := derived1590 a h
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c1519 := derived1519 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1588, some c1600, some c1574, some c1598, some c1597, some c1589, some c1585, some c1599, some c1530, some c305, some c35, some c61, some c425, some c1519, some c1518, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 57) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c1588, c1600, c1574, c1598, c1597, c1589, c1585, c1599, c1530, c305, c35, c61, c425, c1519, c1518] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c1588 := derived1588 a h
  have h1 : Entails.eval a c1600 := derived1600 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c1598 := derived1598 a h
  have h4 : Entails.eval a c1597 := derived1597 a h
  have h5 : Entails.eval a c1589 := derived1589 a h
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c1599 := derived1599 a h
  have h8 : Entails.eval a c1530 := derived1530 a h
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c425 := derived425 a h
  have h13 : Entails.eval a c1519 := derived1519 a h
  have h14 : Entails.eval a c1518 := derived1518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1602, some c1432, some c1585, some c498, some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 57) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1602, c1432, c1585, c498] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1602 := derived1602 a h
  have h1 : Entails.eval a c1432 := derived1432 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c498 := derived498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1603, some c1600, some c322, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 57) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1603, c1600, c322] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1603 := derived1603 a h
  have h1 : Entails.eval a c1600 := derived1600 a h
  have h2 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1605 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1603, some c1600, some c323, some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 57) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c1603, c1600, c323] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c1603 := derived1603 a h
  have h1 : Entails.eval a c1600 := derived1600 a h
  have h2 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1604, some c1602, some c1586, some c158, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 57) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1604, c1602, c1586, c158] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1604 := derived1604 a h
  have h1 : Entails.eval a c1602 := derived1602 a h
  have h2 : Entails.eval a c1586 := derived1586 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1605, some c1574, some c35, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 57) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1605, c1574, c35] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1605 := derived1605 a h
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1605, some c1598, some c1574, some c61, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 57) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1605, c1598, c1574, c61] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1605 := derived1605 a h
  have h1 : Entails.eval a c1598 := derived1598 a h
  have h2 : Entails.eval a c1574 := derived1574 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1606, some c1601, some c205, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 57) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1606, c1601, c205] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1606 := derived1606 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1610 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1607, some c1585, some c1599, some c1519, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 57) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1607, c1585, c1599, c1519] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1607 := derived1607 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1599 := derived1599 a h
  have h3 : Entails.eval a c1519 := derived1519 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1609, some c1598, some c10, some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 57) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1609, c1598, c10] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1609 := derived1609 a h
  have h1 : Entails.eval a c1598 := derived1598 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1611, some c1610, some c1608, some c1599, some c1518]
def p1612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 57) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c1611, c1610, c1608, c1599, c1518] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c1611 := derived1611 a h
  have h1 : Entails.eval a c1610 := derived1610 a h
  have h2 : Entails.eval a c1608 := derived1608 a h
  have h3 : Entails.eval a c1599 := derived1599 a h
  have h4 : Entails.eval a c1518 := derived1518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1612

end CochromaticTwenty.Certificates.B16_1_2
