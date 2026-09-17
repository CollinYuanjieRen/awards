import MerLeanExperiment.Certificates.B16_0_0.Steps1100_1199

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1594 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1587, some c1, some c262, some c263, some c1593, some c1212, some c23, some c108, some c1232, some c1231, some c36, some c1572, some c385, some c387, some c269, some c982, some c222, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 57) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c1564, c1587, c1, c262, c263, c1593, c1212, c23, c108, c1232, c1231, c36, c1572, c385, c387, c269, c982, c222] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c1593 := derived1593 a h
  have h6 : Entails.eval a c1212 := derived1212 a h
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c1232 := derived1232 a h
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c1572 := derived1572 a h
  have h13 : Entails.eval a c385 := h 384 (by decide)
  have h14 : Entails.eval a c387 := h 386 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c982 := derived982 a h
  have h17 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1289, some c186, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 57) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c1564, c1289, c186] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1289 := derived1289 a h
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨34, by decide⟩, true), (⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c128, some c219, some c961, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p1596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 57) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c128, c219, c961] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c128 := h 127 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c961 := derived961 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c22, some c1587, some c109, some c9, some c1594, some c1, some c202, some c156, some c116, some c45, some c1596, some c266, some c34, some c209, some c51, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 57) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c1564, c22, c1587, c109, c9, c1594, c1, c202, c156, c116, c45, c1596, c266, c34, c209, c51] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1594 := derived1594 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c1596 := derived1596 a h
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c209 := h 208 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c22, some c1572, some c1587, some c109, some c9, some c1594, some c1, some c1597, some c114, some c45, some c47, some c116, some c210, some c205, some c315, some c124, some c141, some c266, some c204, some c123, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 57) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1564, c22, c1572, c1587, c109, c9, c1594, c1, c1597, c114, c45, c47, c116, c210, c205, c315, c124, c141, c266, c204, c123] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1572 := derived1572 a h
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1594 := derived1594 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c1597 := derived1597 a h
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c124 := h 123 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c266 := h 265 (by decide)
  have h19 : Entails.eval a c204 := h 203 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨33, by decide⟩, true), (⟨20, by decide⟩, false), (⟨35, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c56, some c1, some c247, some c9, some c1594, some c156, some c1595, some c1183, some c843, some c1235, some c361, some c219, some c344, some c932, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 57) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1564, c56, c1, c247, c9, c1594, c156, c1595, c1183, c843, c1235, c361, c219, c344, c932] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1594 := derived1594 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c1595 := derived1595 a h
  have h8 : Entails.eval a c1183 := derived1183 a h
  have h9 : Entails.eval a c843 := derived843 a h
  have h10 : Entails.eval a c1235 := derived1235 a h
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c932 := derived932 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1600 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c1598, some c265, some c22, some c1572, some c1587, some c109, some c9, some c1594, some c56, some c64, some c247, some c1599, some c114, some c124, some c45, some c47, some c205, some c164, some c148, some c220, some c161, some c359, some c1235, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 57) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1564, c1, c1598, c265, c22, c1572, c1587, c109, c9, c1594, c56, c64, c247, c1599, c114, c124, c45, c47, c205, c164, c148, c220, c161, c359, c1235] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1598 := derived1598 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1572 := derived1572 a h
  have h6 : Entails.eval a c1587 := derived1587 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c1594 := derived1594 a h
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c1599 := derived1599 a h
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c164 := h 163 (by decide)
  have h20 : Entails.eval a c148 := h 147 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  have h23 : Entails.eval a c359 := h 358 (by decide)
  have h24 : Entails.eval a c1235 := derived1235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1587, some c109, some c9, some c1594, some c1, some c22, some c1598, some c265, some c34, some c1600, some c577, some c353, some c1306, some c1183, some c1290, some c344, some c388, some c792, some c192, some c124, some c119, some c202, some c51, some c276, some c135, some c642, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 57) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1564, c1587, c109, c9, c1594, c1, c22, c1598, c265, c34, c1600, c577, c353, c1306, c1183, c1290, c344, c388, c792, c192, c124, c119, c202, c51, c276, c135, c642] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1594 := derived1594 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c1598 := derived1598 a h
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c1600 := derived1600 a h
  have h11 : Entails.eval a c577 := derived577 a h
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c1306 := derived1306 a h
  have h14 : Entails.eval a c1183 := derived1183 a h
  have h15 : Entails.eval a c1290 := derived1290 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c388 := h 387 (by decide)
  have h18 : Entails.eval a c792 := derived792 a h
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c119 := h 118 (by decide)
  have h22 : Entails.eval a c202 := h 201 (by decide)
  have h23 : Entails.eval a c51 := h 50 (by decide)
  have h24 : Entails.eval a c276 := h 275 (by decide)
  have h25 : Entails.eval a c135 := h 134 (by decide)
  have h26 : Entails.eval a c642 := derived642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c1601, some c264, some c1587, some c109, some c9, some c202, some c156, some c1074, some c355, some c160, some c1599, some c128, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 57) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c1564, c1, c1601, c264, c1587, c109, c9, c202, c156, c1074, c355, c160, c1599, c128] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c1587 := derived1587 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c1074 := derived1074 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c1599 := derived1599 a h
  have h13 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c1601, some c264, some c1587, some c109, some c9, some c1594, some c1572, some c1602, some c114, some c1174, some c45, some c47, some c204, some c160, some c148, some c25, some c205, some c124, some c520, some c657, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 57) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1564, c1, c1601, c264, c1587, c109, c9, c1594, c1572, c1602, c114, c1174, c45, c47, c204, c160, c148, c25, c205, c124, c520, c657] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c1587 := derived1587 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c1594 := derived1594 a h
  have h8 : Entails.eval a c1572 := derived1572 a h
  have h9 : Entails.eval a c1602 := derived1602 a h
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c1174 := derived1174 a h
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c520 := derived520 a h
  have h21 : Entails.eval a c657 := derived657 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1329, some c357, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 57) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1329, c357] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1329 := derived1329 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1605 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1587, some c1, some c109, some c9, some c1601, some c1603, some c58, some c69, some c246, some c56, some c792, some c1306, some c192, some c1604, some c1074, some c158, some c354, some c1228, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 57) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c1564, c1587, c1, c109, c9, c1601, c1603, c58, c69, c246, c56, c792, c1306, c192, c1604, c1074, c158, c354, c1228] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1601 := derived1601 a h
  have h6 : Entails.eval a c1603 := derived1603 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c792 := derived792 a h
  have h12 : Entails.eval a c1306 := derived1306 a h
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c1604 := derived1604 a h
  have h15 : Entails.eval a c1074 := derived1074 a h
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c1228 := derived1228 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1587, some c22, some c1572, some c110, some c9, some c1605, some c32, some c1594, some c1, some c156, some c1595, some c1599, some c1183, some c355, some c843, some c219, some c344, some c1259, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 57) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1564, c1587, c22, c1572, c110, c9, c1605, c32, c1594, c1, c156, c1595, c1599, c1183, c355, c843, c219, c344, c1259] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1572 := derived1572 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c1605 := derived1605 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c1594 := derived1594 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c1595 := derived1595 a h
  have h12 : Entails.eval a c1599 := derived1599 a h
  have h13 : Entails.eval a c1183 := derived1183 a h
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c843 := derived843 a h
  have h16 : Entails.eval a c219 := h 218 (by decide)
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c1259 := derived1259 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨18, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c265, some c56, some c64, some c247, some c164, some c59, some c220, some c359, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 57) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1564, c265, c56, c64, c247, c164, c59, c220, c359] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1605, some c1594, some c1587, some c1, some c22, some c32, some c1572, some c265, some c110, some c9, some c1606, some c124, some c1607, some c355, some c353, some c1280, some c219, some c344, some c1183, some c1259, some c843, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 57) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1564, c1605, c1594, c1587, c1, c22, c32, c1572, c265, c110, c9, c1606, c124, c1607, c355, c353, c1280, c219, c344, c1183, c1259, c843] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1605 := derived1605 a h
  have h2 : Entails.eval a c1594 := derived1594 a h
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c1572 := derived1572 a h
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c1606 := derived1606 a h
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c1607 := derived1607 a h
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c1280 := derived1280 a h
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c1183 := derived1183 a h
  have h20 : Entails.eval a c1259 := derived1259 a h
  have h21 : Entails.eval a c843 := derived843 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1587, some c1572, some c110, some c9, some c1608, some c1605, some c1, some c202, some c156, some c4, some c1074, some c1599, some c355, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 57) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1564, c1587, c1572, c110, c9, c1608, c1605, c1, c202, c156, c4, c1074, c1599, c355] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1572 := derived1572 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1608 := derived1608 a h
  have h6 : Entails.eval a c1605 := derived1605 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c1074 := derived1074 a h
  have h12 : Entails.eval a c1599 := derived1599 a h
  have h13 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1610 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1608, some c1605, some c1594, some c1587, some c1, some c1572, some c110, some c9, some c1609, some c114, some c1174, some c47, some c204, some c160, some c141, some c1074, some c272, some c56, some c64, some c246, some c435, some c96, some c247, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 57) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1564, c1608, c1605, c1594, c1587, c1, c1572, c110, c9, c1609, c114, c1174, c47, c204, c160, c141, c1074, c272, c56, c64, c246, c435, c96, c247] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1608 := derived1608 a h
  have h2 : Entails.eval a c1605 := derived1605 a h
  have h3 : Entails.eval a c1594 := derived1594 a h
  have h4 : Entails.eval a c1587 := derived1587 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1572 := derived1572 a h
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c1609 := derived1609 a h
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c1174 := derived1174 a h
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c160 := h 159 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c1074 := derived1074 a h
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c56 := h 55 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c246 := h 245 (by decide)
  have h21 : Entails.eval a c435 := derived435 a h
  have h22 : Entails.eval a c96 := h 95 (by decide)
  have h23 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c1605, some c1608, some c1610, some c58, some c68, some c246, some c56, some c1604, some c354, some c1074, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 57) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1564, c1, c1605, c1608, c1610, c58, c68, c246, c56, c1604, c354, c1074] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1605 := derived1605 a h
  have h3 : Entails.eval a c1608 := derived1608 a h
  have h4 : Entails.eval a c1610 := derived1610 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c1604 := derived1604 a h
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨39, by decide⟩, false), (⟨54, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨16, by decide⟩, false), (⟨49, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c109, some c45, some c9, some c843, some c210, some c165, some c247, some c64, some c942, some c349, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 57) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c1564, c1, c109, c45, c9, c843, c210, c165, c247, c64, c942, c349] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c942 := derived942 a h
  have h11 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1613 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1, some c1587, some c1594, some c1611, some c108, some c1230, some c1231, some c10, some c1096, some c1572, some c204, some c114, some c1174, some c123, some c44, some c266, some c248, some c223, some c212, some c1612, some c1232, some c247, some c210, some c221, some c284, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1613 : lratChecker f1613 p1613 = .success := by decide +kernel
theorem unsat1613 : Unsatisfiable (PosFin 57) f1613 := by
  apply lratCheckerSound f1613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1613
  · intro a ha; simp [p1613] at ha; subst a; trivial
  · exact checked1613
theorem derived1613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1613 := by
  apply localUnsat_implies_entails f1613 [c1564, c1, c1587, c1594, c1611, c108, c1230, c1231, c10, c1096, c1572, c204, c114, c1174, c123, c44, c266, c248, c223, c212, c1612, c1232, c247, c210, c221, c284] c1613 unsat1613 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1594 := derived1594 a h
  have h4 : Entails.eval a c1611 := derived1611 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1230 := derived1230 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1096 := derived1096 a h
  have h10 : Entails.eval a c1572 := derived1572 a h
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c1174 := derived1174 a h
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c212 := h 211 (by decide)
  have h20 : Entails.eval a c1612 := derived1612 a h
  have h21 : Entails.eval a c1232 := derived1232 a h
  have h22 : Entails.eval a c247 := h 246 (by decide)
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c221 := h 220 (by decide)
  have h25 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1614 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c1574, some c112, some c1578, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p1614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1614 : lratChecker f1614 p1614 = .success := by decide +kernel
theorem unsat1614 : Unsatisfiable (PosFin 57) f1614 := by
  apply lratCheckerSound f1614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1614
  · intro a ha; simp [p1614] at ha; subst a; trivial
  · exact checked1614
theorem derived1614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1614 := by
  apply localUnsat_implies_entails f1614 [c2, c1574, c112, c1578] c1614 unsat1614 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c1574 := derived1574 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1578 := derived1578 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1615 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c129, some c199, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1615 : lratChecker f1615 p1615 = .success := by decide +kernel
theorem unsat1615 : Unsatisfiable (PosFin 57) f1615 := by
  apply lratCheckerSound f1615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1615
  · intro a ha; simp [p1615] at ha; subst a; trivial
  · exact checked1615
theorem derived1615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1615 := by
  apply localUnsat_implies_entails f1615 [c131, c129, c199] c1615 unsat1615 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1616 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c152, some c263, some c269, some c1591, some c1615, some c161, some c227, some c225, some c843, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1616 : lratChecker f1616 p1616 = .success := by decide +kernel
theorem unsat1616 : Unsatisfiable (PosFin 57) f1616 := by
  apply lratCheckerSound f1616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1616
  · intro a ha; simp [p1616] at ha; subst a; trivial
  · exact checked1616
theorem derived1616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1616 := by
  apply localUnsat_implies_entails f1616 [c1564, c1613, c152, c263, c269, c1591, c1615, c161, c227, c225, c843] c1616 unsat1616 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c1591 := derived1591 a h
  have h6 : Entails.eval a c1615 := derived1615 a h
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c843 := derived843 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1617 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c198, some c196, some c1174, some c22, some c152, some c56, some c180, some c1614, some c109, some c33, some c1616, some c123, some c114, some c266, some c45, some c34, some c124, some c199, some c183, some c135, some c81, some c87, some c170, some c369, some c1239, some c382, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1617 : lratChecker f1617 p1617 = .success := by decide +kernel
theorem unsat1617 : Unsatisfiable (PosFin 57) f1617 := by
  apply lratCheckerSound f1617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1617
  · intro a ha; simp [p1617] at ha; subst a; trivial
  · exact checked1617
theorem derived1617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1617 := by
  apply localUnsat_implies_entails f1617 [c1564, c1613, c198, c196, c1174, c22, c152, c56, c180, c1614, c109, c33, c1616, c123, c114, c266, c45, c34, c124, c199, c183, c135, c81, c87, c170, c369, c1239, c382] c1617 unsat1617 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c1174 := derived1174 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c1614 := derived1614 a h
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c1616 := derived1616 a h
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c183 := h 182 (by decide)
  have h21 : Entails.eval a c135 := h 134 (by decide)
  have h22 : Entails.eval a c81 := h 80 (by decide)
  have h23 : Entails.eval a c87 := h 86 (by decide)
  have h24 : Entails.eval a c170 := h 169 (by decide)
  have h25 : Entails.eval a c369 := h 368 (by decide)
  have h26 : Entails.eval a c1239 := derived1239 a h
  have h27 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1618 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c198, some c196, some c1174, some c22, some c152, some c56, some c180, some c1617, some c32, some c96, some c247, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1618 : lratChecker f1618 p1618 = .success := by decide +kernel
theorem unsat1618 : Unsatisfiable (PosFin 57) f1618 := by
  apply lratCheckerSound f1618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1618
  · intro a ha; simp [p1618] at ha; subst a; trivial
  · exact checked1618
theorem derived1618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1618 := by
  apply localUnsat_implies_entails f1618 [c1564, c1613, c198, c196, c1174, c22, c152, c56, c180, c1617, c32, c96, c247] c1618 unsat1618 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c1174 := derived1174 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c1617 := derived1617 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1619 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c152, some c56, some c1618, some c196, some c553, some c2, some c111, some c245, some c1182, some c57, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 57) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c1564, c1613, c152, c56, c1618, c196, c553, c2, c111, c245, c1182, c57] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c1618 := derived1618 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c553 := derived553 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c1182 := derived1182 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1620 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c56, some c263, some c245, some c344, some c932, some c388, some c224, some c982, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 57) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c1564, c56, c263, c245, c344, c932, c388, c224, c982] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c932 := derived932 a h
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c982 := derived982 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1618, some c1613, some c196, some c198, some c152, some c56, some c1619, some c109, some c108, some c64, some c1182, some c1158, some c1620, some c123, some c266, some c248, some c220, some c344, some c843, some c385, some c349, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 57) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c1564, c1618, c1613, c196, c198, c152, c56, c1619, c109, c108, c64, c1182, c1158, c1620, c123, c266, c248, c220, c344, c843, c385, c349] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1618 := derived1618 a h
  have h2 : Entails.eval a c1613 := derived1613 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c1619 := derived1619 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c1182 := derived1182 a h
  have h12 : Entails.eval a c1158 := derived1158 a h
  have h13 : Entails.eval a c1620 := derived1620 a h
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c843 := derived843 a h
  have h20 : Entails.eval a c385 := h 384 (by decide)
  have h21 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1621, some c1618, some c1613, some c198, some c196, some c1174, some c553, some c2, some c111, some c263, some c1230, some c1231, some c221, some c245, some c57, some c360, some c354, some c64, some c222, some c112, some c269, some c1573, some c38, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 57) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1564, c1621, c1618, c1613, c198, c196, c1174, c553, c2, c111, c263, c1230, c1231, c221, c245, c57, c360, c354, c64, c222, c112, c269, c1573, c38] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1618 := derived1618 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c1174 := derived1174 a h
  have h7 : Entails.eval a c553 := derived553 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c1230 := derived1230 a h
  have h12 : Entails.eval a c1231 := derived1231 a h
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c222 := h 221 (by decide)
  have h20 : Entails.eval a c112 := h 111 (by decide)
  have h21 : Entails.eval a c269 := h 268 (by decide)
  have h22 : Entails.eval a c1573 := derived1573 a h
  have h23 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c223, some c348, some c249, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 57) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c223, c348, c249] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c223 := h 222 (by decide)
  have h1 : Entails.eval a c348 := h 347 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1618, some c1613, some c198, some c196, some c1174, some c1621, some c1622, some c109, some c108, some c1231, some c180, some c1623, some c843, some c221, some c346, some c247, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 57) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1564, c1618, c1613, c198, c196, c1174, c1621, c1622, c109, c108, c1231, c180, c1623, c843, c221, c346, c247] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1618 := derived1618 a h
  have h2 : Entails.eval a c1613 := derived1613 a h
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c1174 := derived1174 a h
  have h6 : Entails.eval a c1621 := derived1621 a h
  have h7 : Entails.eval a c1622 := derived1622 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c1623 := derived1623 a h
  have h13 : Entails.eval a c843 := derived843 a h
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c346 := h 345 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c1618, some c1624, some c1586, some c108, some c1231, some c1232, some c181, some c247, some c4, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 57) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1564, c1613, c1618, c1624, c1586, c108, c1231, c1232, c181, c247, c4] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1618 := derived1618 a h
  have h3 : Entails.eval a c1624 := derived1624 a h
  have h4 : Entails.eval a c1586 := derived1586 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1231 := derived1231 a h
  have h7 : Entails.eval a c1232 := derived1232 a h
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c196, some c198, some c1625, some c20, some c152, some c22, some c1559, some c1326, some c112, some c12, some c70, some c155, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 57) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1564, c1613, c196, c198, c1625, c20, c152, c22, c1559, c1326, c112, c12, c70, c155] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c1625 := derived1625 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1559 := derived1559 a h
  have h9 : Entails.eval a c1326 := derived1326 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1625, some c28, some c1613, some c196, some c198, some c20, some c152, some c22, some c1559, some c58, some c1604, some c1209, some c250, some c268, some c344, some c254, some c128, some c224, some c153, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 57) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1564, c1625, c28, c1613, c196, c198, c20, c152, c22, c1559, c58, c1604, c1209, c250, c268, c344, c254, c128, c224, c153] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1625 := derived1625 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c1559 := derived1559 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c1604 := derived1604 a h
  have h12 : Entails.eval a c1209 := derived1209 a h
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c344 := h 343 (by decide)
  have h16 : Entails.eval a c254 := h 253 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c1625, some c20, some c152, some c58, some c180, some c1604, some c1306, some c22, some c196, some c198, some c1626, some c109, some c792, some c28, some c393, some c258, some c1627, some c123, some c124, some c254, some c155, some c349, some c220, some c354, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 57) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1564, c1613, c1625, c20, c152, c58, c180, c1604, c1306, c22, c196, c198, c1626, c109, c792, c28, c393, c258, c1627, c123, c124, c254, c155, c349, c220, c354] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c1604 := derived1604 a h
  have h8 : Entails.eval a c1306 := derived1306 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c1626 := derived1626 a h
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c792 := derived792 a h
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c393 := h 392 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c1627 := derived1627 a h
  have h19 : Entails.eval a c123 := h 122 (by decide)
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c254 := h 253 (by decide)
  have h22 : Entails.eval a c155 := h 154 (by decide)
  have h23 : Entails.eval a c349 := h 348 (by decide)
  have h24 : Entails.eval a c220 := h 219 (by decide)
  have h25 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c1625, some c20, some c152, some c196, some c198, some c22, some c1604, some c58, some c1559, some c180, some c29, some c1628, some c68, some c356, some c354, some c70, some c1310, some c1302, some c110, some c1627, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 57) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c1564, c1613, c1625, c20, c152, c196, c198, c22, c1604, c58, c1559, c180, c29, c1628, c68, c356, c354, c70, c1310, c1302, c110, c1627] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1604 := derived1604 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c1559 := derived1559 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c1628 := derived1628 a h
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c356 := h 355 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c1310 := derived1310 a h
  have h19 : Entails.eval a c1302 := derived1302 a h
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c1627 := derived1627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1629, some c1625, some c1613, some c196, some c553, some c2, some c111, some c1231, some c1187, some c112, some c12, some c1233, some c183, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 57) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c1564, c1629, c1625, c1613, c196, c553, c2, c111, c1231, c1187, c112, c12, c1233, c183] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c553 := derived553 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c1187 := derived1187 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1233 := derived1233 a h
  have h13 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1629, some c1613, some c1625, some c20, some c152, some c196, some c198, some c1630, some c109, some c108, some c28, some c29, some c1187, some c1559, some c114, some c44, some c45, some c210, some c271, some c223, some c124, some c155, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 57) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c1564, c1629, c1613, c1625, c20, c152, c196, c198, c1630, c109, c108, c28, c29, c1187, c1559, c114, c44, c45, c210, c271, c223, c124, c155] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1613 := derived1613 a h
  have h3 : Entails.eval a c1625 := derived1625 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c1630 := derived1630 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c1187 := derived1187 a h
  have h14 : Entails.eval a c1559 := derived1559 a h
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c223 := h 222 (by decide)
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1631, some c1629, some c1613, some c1625, some c20, some c152, some c196, some c553, some c2, some c111, some c1231, some c29, some c1232, some c267, some c269, some c385, some c222, some c57, some c1144, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 57) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c1564, c1631, c1629, c1613, c1625, c20, c152, c196, c553, c2, c111, c1231, c29, c1232, c267, c269, c385, c222, c57, c1144] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1631 := derived1631 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c1625 := derived1625 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c553 := derived553 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c1232 := derived1232 a h
  have h14 : Entails.eval a c267 := h 266 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c222 := h 221 (by decide)
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c1144 := derived1144 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1613, some c1625, some c20, some c152, some c1629, some c1632, some c108, some c1231, some c180, some c1631, some c1232, some c387, some c348, some c155, some c181, some c17, some c196, some c198, some c29, some c1559, some c1230, some c1187, some c269, some c222, some c165, some c1160, some c117, some c143, some c46, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 57) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c1564, c1613, c1625, c20, c152, c1629, c1632, c108, c1231, c180, c1631, c1232, c387, c348, c155, c181, c17, c196, c198, c29, c1559, c1230, c1187, c269, c222, c165, c1160, c117, c143, c46] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c1629 := derived1629 a h
  have h6 : Entails.eval a c1632 := derived1632 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c1631 := derived1631 a h
  have h11 : Entails.eval a c1232 := derived1232 a h
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c181 := h 180 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c196 := h 195 (by decide)
  have h18 : Entails.eval a c198 := h 197 (by decide)
  have h19 : Entails.eval a c29 := h 28 (by decide)
  have h20 : Entails.eval a c1559 := derived1559 a h
  have h21 : Entails.eval a c1230 := derived1230 a h
  have h22 : Entails.eval a c1187 := derived1187 a h
  have h23 : Entails.eval a c269 := h 268 (by decide)
  have h24 : Entails.eval a c222 := h 221 (by decide)
  have h25 : Entails.eval a c165 := h 164 (by decide)
  have h26 : Entails.eval a c1160 := derived1160 a h
  have h27 : Entails.eval a c117 := h 116 (by decide)
  have h28 : Entails.eval a c143 := h 142 (by decide)
  have h29 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c198, some c196, some c1625, some c20, some c152, some c1629, some c1631, some c1632, some c108, some c1231, some c29, some c1232, some c180, some c1559, some c181, some c387, some c4, some c348, some c155, some c1633, some c114, some c124, some c44, some c271, some c211, some c28, some c46, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 57) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c1564, c198, c196, c1625, c20, c152, c1629, c1631, c1632, c108, c1231, c29, c1232, c180, c1559, c181, c387, c4, c348, c155, c1633, c114, c124, c44, c271, c211, c28, c46] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c1625 := derived1625 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c1629 := derived1629 a h
  have h7 : Entails.eval a c1631 := derived1631 a h
  have h8 : Entails.eval a c1632 := derived1632 a h
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c1231 := derived1231 a h
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c1232 := derived1232 a h
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c1559 := derived1559 a h
  have h15 : Entails.eval a c181 := h 180 (by decide)
  have h16 : Entails.eval a c387 := h 386 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c155 := h 154 (by decide)
  have h20 : Entails.eval a c1633 := derived1633 a h
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  have h24 : Entails.eval a c271 := h 270 (by decide)
  have h25 : Entails.eval a c211 := h 210 (by decide)
  have h26 : Entails.eval a c28 := h 27 (by decide)
  have h27 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1613, some c1634, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 57) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1613, c1634] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1613 := derived1613 a h
  have h1 : Entails.eval a c1634 := derived1634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1636 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c3, some c246, some c262, some c31, some c98, some c249, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 57) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c1635, c3, c246, c262, c31, c98, c249] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c246 := h 245 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c3, some c262, some c21, some c1357, some c2, some c358, some c353, some c1234, some c1636, some c112, some c1063, some c625, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 57) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c1564, c1635, c3, c262, c21, c1357, c2, c358, c353, c1234, c1636, c112, c1063, c625] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c1234 := derived1234 a h
  have h10 : Entails.eval a c1636 := derived1636 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c1063 := derived1063 a h
  have h13 : Entails.eval a c625 := derived625 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c3, some c262, some c21, some c2, some c264, some c58, some c246, some c1066, some c56, some c1570, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 57) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c1635, c1564, c3, c262, c21, c2, c264, c58, c246, c1066, c56, c1570] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c1066 := derived1066 a h
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c1570 := derived1570 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c3, some c262, some c2, some c21, some c1638, some c358, some c353, some c1637, some c1234, some c13, some c1065, some c157, some c96, some c23, some c247, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 57) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1564, c1635, c3, c262, c2, c21, c1638, c358, c353, c1637, c1234, c13, c1065, c157, c96, c23, c247] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c1638 := derived1638 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c1637 := derived1637 a h
  have h10 : Entails.eval a c1234 := derived1234 a h
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c1065 := derived1065 a h
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨10, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1639, some c109, some c14, some c202, some c1083, some c3, some c1255, some c116, some c45, some c1079, some c281, some c134, some c229, some c238, some c169, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 57) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c1635, c1639, c109, c14, c202, c1083, c3, c1255, c116, c45, c1079, c281, c134, c229, c238, c169] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1083 := derived1083 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c1255 := derived1255 a h
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c1079 := derived1079 a h
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c238 := h 237 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨10, by decide⟩, false), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1639, some c109, some c14, some c3, some c56, some c64, some c158, some c1074, some c361, some c1640, some c247, some c1183, some c1235, some c843, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 57) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1635, c1564, c1639, c109, c14, c3, c56, c64, c158, c1074, c361, c1640, c247, c1183, c1235, c843] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c1074 := derived1074 a h
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c1640 := derived1640 a h
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c1183 := derived1183 a h
  have h14 : Entails.eval a c1235 := derived1235 a h
  have h15 : Entails.eval a c843 := derived843 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c3, some c1604, some c353, some c1074, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 57) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c1635, c3, c1604, c353, c1074] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1604 := derived1604 a h
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c190, some c1235, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 57) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c162, c190, c1235] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c1235 := derived1235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, true), (⟨9, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c623, some c135, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 57) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c1635, c623, c135] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c623 := derived623 a h
  have h2 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1639, some c109, some c14, some c3, some c262, some c1642, some c56, some c64, some c1641, some c246, some c114, some c97, some c45, some c1644, some c205, some c162, some c1643, some c1227, some c361, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 57) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c1635, c1564, c1639, c109, c14, c3, c262, c1642, c56, c64, c1641, c246, c114, c97, c45, c1644, c205, c162, c1643, c1227, c361] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c1642 := derived1642 a h
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c1641 := derived1641 a h
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c1644 := derived1644 a h
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c1643 := derived1643 a h
  have h19 : Entails.eval a c1227 := derived1227 a h
  have h20 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1639, some c3, some c109, some c14, some c1645, some c58, some c69, some c246, some c56, some c792, some c1306, some c1604, some c192, some c1074, some c881, some c1228, some c1240, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 57) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c1635, c1564, c1639, c3, c109, c14, c1645, c58, c69, c246, c56, c792, c1306, c1604, c192, c1074, c881, c1228, c1240] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c1645 := derived1645 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c792 := derived792 a h
  have h12 : Entails.eval a c1306 := derived1306 a h
  have h13 : Entails.eval a c1604 := derived1604 a h
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c1074 := derived1074 a h
  have h16 : Entails.eval a c881 := derived881 a h
  have h17 : Entails.eval a c1228 := derived1228 a h
  have h18 : Entails.eval a c1240 := derived1240 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c3, some c1642, some c56, some c246, some c96, some c385, some c387, some c247, some c23, some c982, some c64, some c110, some c1182, some c1158, some c1074, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 57) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1635, c1564, c3, c1642, c56, c246, c96, c385, c387, c247, c23, c982, c64, c110, c1182, c1158, c1074] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1642 := derived1642 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c982 := derived982 a h
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c1182 := derived1182 a h
  have h15 : Entails.eval a c1158 := derived1158 a h
  have h16 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c3, some c1639, some c1646, some c1647, some c58, some c68, some c246, some c56, some c1604, some c354, some c1074, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 57) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1635, c1564, c3, c1639, c1646, c1647, c58, c68, c246, c56, c1604, c354, c1074] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1639 := derived1639 a h
  have h4 : Entails.eval a c1646 := derived1646 a h
  have h5 : Entails.eval a c1647 := derived1647 a h
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c1604 := derived1604 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c21, some c245, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 57) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c57, c21, c245] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c56, some c112, some c957, some c932, some c388, some c30, some c95, some c245, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 57) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c1564, c56, c112, c957, c932, c388, c30, c95, c245] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c957 := derived957 a h
  have h4 : Entails.eval a c932 := derived932 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c115, some c1648, some c56, some c1649, some c1182, some c358, some c277, some c111, some c1650, some c9, some c64, some c158, some c133, some c2, some c228, some c330, some c332, some c263, some c132, some c125, some c301, some c1643, some c368, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 57) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c1564, c1635, c115, c1648, c56, c1649, c1182, c358, c277, c111, c1650, c9, c64, c158, c133, c2, c228, c330, c332, c263, c132, c125, c301, c1643, c368] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1648 := derived1648 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c1182 := derived1182 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c277 := h 276 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c1650 := derived1650 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c158 := h 157 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c330 := h 329 (by decide)
  have h18 : Entails.eval a c332 := h 331 (by decide)
  have h19 : Entails.eval a c263 := h 262 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  have h21 : Entails.eval a c125 := h 124 (by decide)
  have h22 : Entails.eval a c301 := h 300 (by decide)
  have h23 : Entails.eval a c1643 := derived1643 a h
  have h24 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c353, some c355, some c1649, some c66, some c1231, some c111, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 57) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c1564, c353, c355, c1649, c66, c1231, c111] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c1649 := derived1649 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1653 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1648, some c1652, some c56, some c1651, some c1649, some c1357, some c1182, some c111, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 57) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c1564, c1648, c1652, c56, c1651, c1649, c1357, c1182, c111] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c1652 := derived1652 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c1651 := derived1651 a h
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c1357 := derived1357 a h
  have h7 : Entails.eval a c1182 := derived1182 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1654 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1648, some c1653, some c108, some c109, some c1230, some c10, some c1182, some c1158, some c9, some c165, some c1074, some c203, some c64, some c1141, some c115, some c114, some c273, some c133, some c132, some c228, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 57) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1564, c1635, c1648, c1653, c108, c109, c1230, c10, c1182, c1158, c9, c165, c1074, c203, c64, c1141, c115, c114, c273, c133, c132, c228] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c1653 := derived1653 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c1230 := derived1230 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1182 := derived1182 a h
  have h9 : Entails.eval a c1158 := derived1158 a h
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c1074 := derived1074 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c1141 := derived1141 a h
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  have h21 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨19, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c56, some c1649, some c1654, some c1648, some c112, some c1650, some c111, some c1230, some c10, some c1233, some c360, some c159, some c525, some c222, some c2, some c38, some c269, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 57) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1564, c56, c1649, c1654, c1648, c112, c1650, c111, c1230, c10, c1233, c360, c159, c525, c222, c2, c38, c269] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c1649 := derived1649 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1648 := derived1648 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1650 := derived1650 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1230 := derived1230 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c1233 := derived1233 a h
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c222 := h 221 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c56, some c1649, some c1654, some c1655, some c9, some c64, some c158, some c359, some c2, some c221, some c263, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 57) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1564, c56, c1649, c1654, c1655, c9, c64, c158, c359, c2, c221, c263] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c1649 := derived1649 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1655 := derived1655 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1648, some c56, some c1649, some c1656, some c262, some c1357, some c2, some c111, some c1230, some c10, some c159, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 57) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1564, c1648, c56, c1649, c1656, c262, c1357, c2, c111, c1230, c10, c159] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c1649 := derived1649 a h
  have h4 : Entails.eval a c1656 := derived1656 a h
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c1357 := derived1357 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c1230 := derived1230 a h
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1657, some c1654, some c57, some c21, some c1649, some c263, some c125, some c221, some c445, some c112, some c428, some c9, some c252, some c162, some c222, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 57) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c1635, c1564, c1657, c1654, c57, c21, c1649, c263, c125, c221, c445, c112, c428, c9, c252, c162, c222] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1657 := derived1657 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c1649 := derived1649 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c445 := derived445 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c428 := derived428 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c162 := h 161 (by decide)
  have h16 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1657, some c1654, some c1648, some c1658, some c354, some c221, some c265, some c263, some c31, some c577, some c2, some c112, some c9, some c1240, some c203, some c73, some c10, some c111, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 57) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1564, c1657, c1654, c1648, c1658, c354, c221, c265, c263, c31, c577, c2, c112, c9, c1240, c203, c73, c10, c111] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1657 := derived1657 a h
  have h2 : Entails.eval a c1654 := derived1654 a h
  have h3 : Entails.eval a c1648 := derived1648 a h
  have h4 : Entails.eval a c1658 := derived1658 a h
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c577 := derived577 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c1240 := derived1240 a h
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1648, some c1659, some c262, some c1357, some c2, some c21, some c111, some c1230, some c10, some c159, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 57) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c1564, c1648, c1659, c262, c1357, c2, c21, c111, c1230, c10, c159] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c1659 := derived1659 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1230 := derived1230 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1660, some c109, some c1648, some c108, some c1230, some c9, some c10, some c165, some c60, some c203, some c1231, some c1141, some c115, some c133, some c114, some c81, some c80, some c228, some c172, some c132, some c190, some c301, some c367, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 57) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c1564, c1635, c1660, c109, c1648, c108, c1230, c9, c10, c165, c60, c203, c1231, c1141, c115, c133, c114, c81, c80, c228, c172, c132, c190, c301, c367] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1660 := derived1660 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1648 := derived1648 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1230 := derived1230 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c1231 := derived1231 a h
  have h13 : Entails.eval a c1141 := derived1141 a h
  have h14 : Entails.eval a c115 := h 114 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c80 := h 79 (by decide)
  have h19 : Entails.eval a c228 := h 227 (by decide)
  have h20 : Entails.eval a c172 := h 171 (by decide)
  have h21 : Entails.eval a c132 := h 131 (by decide)
  have h22 : Entails.eval a c190 := h 189 (by decide)
  have h23 : Entails.eval a c301 := h 300 (by decide)
  have h24 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1648, some c1654, some c1660, some c108, some c109, some c1230, some c1231, some c10, some c9, some c165, some c203, some c64, some c60, some c1661, some c262, some c246, some c1174, some c114, some c167, some c44, some c45, some c1074, some c144, some c354, some c190, some c346, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 57) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c1564, c1635, c1648, c1654, c1660, c108, c109, c1230, c1231, c10, c9, c165, c203, c64, c60, c1661, c262, c246, c1174, c114, c167, c44, c45, c1074, c144, c354, c190, c346] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1660 := derived1660 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1230 := derived1230 a h
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  have h15 : Entails.eval a c1661 := derived1661 a h
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c246 := h 245 (by decide)
  have h18 : Entails.eval a c1174 := derived1174 a h
  have h19 : Entails.eval a c114 := h 113 (by decide)
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c44 := h 43 (by decide)
  have h22 : Entails.eval a c45 := h 44 (by decide)
  have h23 : Entails.eval a c1074 := derived1074 a h
  have h24 : Entails.eval a c144 := h 143 (by decide)
  have h25 : Entails.eval a c354 := h 353 (by decide)
  have h26 : Entails.eval a c190 := h 189 (by decide)
  have h27 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c30, some c35, some c263, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 57) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1585, c30, c35, c263] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1662, some c1648, some c56, some c1649, some c1663, some c111, some c1230, some c10, some c1232, some c159, some c247, some c2, some c1582, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 57) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1564, c1662, c1648, c56, c1649, c1663, c111, c1230, c10, c1232, c159, c247, c2, c1582] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c1649 := derived1649 a h
  have h5 : Entails.eval a c1663 := derived1663 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1230 := derived1230 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1232 := derived1232 a h
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c1582 := derived1582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1648, some c1664, some c1652, some c1662, some c21, some c1649, some c263, some c1231, some c221, some c111, some c356, some c1394, some c223, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 57) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c1564, c1648, c1664, c1652, c1662, c21, c1649, c263, c1231, c221, c111, c356, c1394, c223] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c1664 := derived1664 a h
  have h3 : Entails.eval a c1652 := derived1652 a h
  have h4 : Entails.eval a c1662 := derived1662 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c1649 := derived1649 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c1394 := derived1394 a h
  have h13 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1662, some c1648, some c1664, some c1665, some c354, some c59, some c23, some c265, some c247, some c577, some c1231, some c71, some c111, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 57) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1564, c1662, c1648, c1664, c1665, c354, c59, c23, c265, c247, c577, c1231, c71, c111] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c1664 := derived1664 a h
  have h4 : Entails.eval a c1665 := derived1665 a h
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c577 := derived577 a h
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1667 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1648, some c1666, some c262, some c1357, some c2, some c21, some c111, some c1230, some c10, some c159, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 57) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1564, c1648, c1666, c262, c1357, c2, c21, c111, c1230, c10, c159] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c1666 := derived1666 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c1357 := derived1357 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1230 := derived1230 a h
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c115, some c1667, some c1141, some c1648, some c108, some c1662, some c1232, some c1231, some c387, some c1233, some c247, some c127, some c1394, some c266, some c48, some c597, some c213, some c208, some c291, some c302, some c228, some c132, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 57) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1564, c1635, c115, c1667, c1141, c1648, c108, c1662, c1232, c1231, c387, c1233, c247, c127, c1394, c266, c48, c597, c213, c208, c291, c302, c228, c132] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1667 := derived1667 a h
  have h4 : Entails.eval a c1141 := derived1141 a h
  have h5 : Entails.eval a c1648 := derived1648 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1662 := derived1662 a h
  have h8 : Entails.eval a c1232 := derived1232 a h
  have h9 : Entails.eval a c1231 := derived1231 a h
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c1233 := derived1233 a h
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c127 := h 126 (by decide)
  have h14 : Entails.eval a c1394 := derived1394 a h
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c597 := derived597 a h
  have h18 : Entails.eval a c213 := h 212 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c291 := h 290 (by decide)
  have h21 : Entails.eval a c302 := h 301 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  have h23 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1648, some c1667, some c108, some c1662, some c1232, some c1231, some c247, some c36, some c4, some c23, some c387, some c385, some c10, some c1230, some c1141, some c1668, some c163, some c205, some c345, some c126, some c159, some c269, some c114, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 57) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1564, c1635, c1648, c1667, c108, c1662, c1232, c1231, c247, c36, c4, c23, c387, c385, c10, c1230, c1141, c1668, c163, c205, c345, c126, c159, c269, c114] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c1667 := derived1667 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1662 := derived1662 a h
  have h6 : Entails.eval a c1232 := derived1232 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c385 := h 384 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c1230 := derived1230 a h
  have h16 : Entails.eval a c1141 := derived1141 a h
  have h17 : Entails.eval a c1668 := derived1668 a h
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c126 := h 125 (by decide)
  have h22 : Entails.eval a c159 := h 158 (by decide)
  have h23 : Entails.eval a c269 := h 268 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1662, some c1648, some c1667, some c108, some c1232, some c1231, some c247, some c1669, some c264, some c35, some c4, some c23, some c387, some c1233, some c385, some c10, some c1230, some c1074, some c345, some c167, some c163, some c118, some c48, some c54, some c146, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 57) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c1564, c1635, c1662, c1648, c1667, c108, c1232, c1231, c247, c1669, c264, c35, c4, c23, c387, c1233, c385, c10, c1230, c1074, c345, c167, c163, c118, c48, c54, c146] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1662 := derived1662 a h
  have h3 : Entails.eval a c1648 := derived1648 a h
  have h4 : Entails.eval a c1667 := derived1667 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1232 := derived1232 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c1669 := derived1669 a h
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c387 := h 386 (by decide)
  have h15 : Entails.eval a c1233 := derived1233 a h
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c10 := h 9 (by decide)
  have h18 : Entails.eval a c1230 := derived1230 a h
  have h19 : Entails.eval a c1074 := derived1074 a h
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c118 := h 117 (by decide)
  have h24 : Entails.eval a c48 := h 47 (by decide)
  have h25 : Entails.eval a c54 := h 53 (by decide)
  have h26 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1648, some c1662, some c1667, some c108, some c1230, some c1231, some c10, some c1232, some c385, some c387, some c247, some c23, some c4, some c982, some c1669, some c262, some c246, some c1670, some c1182, some c159, some c354, some c347, some c114, some c64, some c190, some c44, some c46, some c145, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 57) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1635, c1564, c1648, c1662, c1667, c108, c1230, c1231, c10, c1232, c385, c387, c247, c23, c4, c982, c1669, c262, c246, c1670, c1182, c159, c354, c347, c114, c64, c190, c44, c46, c145] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1648 := derived1648 a h
  have h3 : Entails.eval a c1662 := derived1662 a h
  have h4 : Entails.eval a c1667 := derived1667 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1230 := derived1230 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1232 := derived1232 a h
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c982 := derived982 a h
  have h16 : Entails.eval a c1669 := derived1669 a h
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c246 := h 245 (by decide)
  have h19 : Entails.eval a c1670 := derived1670 a h
  have h20 : Entails.eval a c1182 := derived1182 a h
  have h21 : Entails.eval a c159 := h 158 (by decide)
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c347 := h 346 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c64 := h 63 (by decide)
  have h26 : Entails.eval a c190 := h 189 (by decide)
  have h27 : Entails.eval a c44 := h 43 (by decide)
  have h28 : Entails.eval a c46 := h 45 (by decide)
  have h29 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c3, some c262, some c1671, some c2, some c21, some c1481, some c151, some c56, some c1636, some c112, some c1063, some c14, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 57) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1564, c1635, c3, c262, c1671, c2, c21, c1481, c151, c56, c1636, c112, c1063, c14] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c1481 := derived1481 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c1636 := derived1636 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c1063 := derived1063 a h
  have h13 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1672, some c3, some c1604, some c56, some c246, some c58, some c1647, some c109, some c14, some c361, some c64, some c97, some c1643, some c387, some c247, some c98, some c1236, some c116, some c164, some c45, some c51, some c1079, some c146, some c281, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 57) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c1564, c1635, c1672, c3, c1604, c56, c246, c58, c1647, c109, c14, c361, c64, c97, c1643, c387, c247, c98, c1236, c116, c164, c45, c51, c1079, c146, c281] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1672 := derived1672 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1604 := derived1604 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c1647 := derived1647 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c1643 := derived1643 a h
  have h15 : Entails.eval a c387 := h 386 (by decide)
  have h16 : Entails.eval a c247 := h 246 (by decide)
  have h17 : Entails.eval a c98 := h 97 (by decide)
  have h18 : Entails.eval a c1236 := derived1236 a h
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c164 := h 163 (by decide)
  have h21 : Entails.eval a c45 := h 44 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c1079 := derived1079 a h
  have h24 : Entails.eval a c146 := h 145 (by decide)
  have h25 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1674 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1672, some c3, some c262, some c1074, some c1604, some c56, some c246, some c58, some c1647, some c361, some c109, some c1673, some c1235, some c843, some c220, some c1236, some c249, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1674 : lratChecker f1674 p1674 = .success := by decide +kernel
theorem unsat1674 : Unsatisfiable (PosFin 57) f1674 := by
  apply lratCheckerSound f1674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1674
  · intro a ha; simp [p1674] at ha; subst a; trivial
  · exact checked1674
theorem derived1674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1674 := by
  apply localUnsat_implies_entails f1674 [c1635, c1564, c1672, c3, c262, c1074, c1604, c56, c246, c58, c1647, c361, c109, c1673, c1235, c843, c220, c1236, c249] c1674 unsat1674 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1672 := derived1672 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c1074 := derived1074 a h
  have h6 : Entails.eval a c1604 := derived1604 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c1647 := derived1647 a h
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c1673 := derived1673 a h
  have h14 : Entails.eval a c1235 := derived1235 a h
  have h15 : Entails.eval a c843 := derived843 a h
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c1236 := derived1236 a h
  have h18 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1675 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1672, some c109, some c14, some c1674, some c3, some c262, some c56, some c64, some c246, some c359, some c360, some c158, some c97, some c1235, some c114, some c1643, some c247, some c45, some c116, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1675 : lratChecker f1675 p1675 = .success := by decide +kernel
theorem unsat1675 : Unsatisfiable (PosFin 57) f1675 := by
  apply lratCheckerSound f1675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1675
  · intro a ha; simp [p1675] at ha; subst a; trivial
  · exact checked1675
theorem derived1675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1675 := by
  apply localUnsat_implies_entails f1675 [c1635, c1564, c1672, c109, c14, c1674, c3, c262, c56, c64, c246, c359, c360, c158, c97, c1235, c114, c1643, c247, c45, c116] c1675 unsat1675 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1672 := derived1672 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c1674 := derived1674 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c158 := h 157 (by decide)
  have h14 : Entails.eval a c97 := h 96 (by decide)
  have h15 : Entails.eval a c1235 := derived1235 a h
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c1643 := derived1643 a h
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1676 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1674, some c1672, some c3, some c1671, some c109, some c1675, some c151, some c1604, some c1642, some c354, some c1174, some c1228, some c200, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1676 : lratChecker f1676 p1676 = .success := by decide +kernel
theorem unsat1676 : Unsatisfiable (PosFin 57) f1676 := by
  apply lratCheckerSound f1676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1676
  · intro a ha; simp [p1676] at ha; subst a; trivial
  · exact checked1676
theorem derived1676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1676 := by
  apply localUnsat_implies_entails f1676 [c1635, c1564, c1674, c1672, c3, c1671, c109, c1675, c151, c1604, c1642, c354, c1174, c1228, c200] c1676 unsat1676 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1672 := derived1672 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1675 := derived1675 a h
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c1604 := derived1604 a h
  have h10 : Entails.eval a c1642 := derived1642 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c1174 := derived1174 a h
  have h13 : Entails.eval a c1228 := derived1228 a h
  have h14 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1677 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1671, some c3, some c1672, some c1676, some c13, some c1647, some c58, some c68, some c246, some c153, some c56, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1677 : lratChecker f1677 p1677 = .success := by decide +kernel
theorem unsat1677 : Unsatisfiable (PosFin 57) f1677 := by
  apply lratCheckerSound f1677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1677
  · intro a ha; simp [p1677] at ha; subst a; trivial
  · exact checked1677
theorem derived1677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1677 := by
  apply localUnsat_implies_entails f1677 [c1635, c1564, c1671, c3, c1672, c1676, c13, c1647, c58, c68, c246, c153, c56] c1677 unsat1677 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1672 := derived1672 a h
  have h5 : Entails.eval a c1676 := derived1676 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c1647 := derived1647 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1678 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1677, some c1671, some c21, some c1649, some c263, some c56, some c125, some c1652, some c153, some c221, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1678 : lratChecker f1678 p1678 = .success := by decide +kernel
theorem unsat1678 : Unsatisfiable (PosFin 57) f1678 := by
  apply lratCheckerSound f1678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1678
  · intro a ha; simp [p1678] at ha; subst a; trivial
  · exact checked1678
theorem derived1678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1678 := by
  apply localUnsat_implies_entails f1678 [c1564, c1635, c1677, c1671, c21, c1649, c263, c56, c125, c1652, c153, c221] c1678 unsat1678 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1677 := derived1677 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1649 := derived1649 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c1652 := derived1652 a h
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1679 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c56, some c1678, some c1671, some c263, some c245, some c125, some c199, some c1330, some c181, some c127, some c112, some c249, some c64, some c982, some c360, some c1235, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1679 : lratChecker f1679 p1679 = .success := by decide +kernel
theorem unsat1679 : Unsatisfiable (PosFin 57) f1679 := by
  apply lratCheckerSound f1679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1679
  · intro a ha; simp [p1679] at ha; subst a; trivial
  · exact checked1679
theorem derived1679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1679 := by
  apply localUnsat_implies_entails f1679 [c1635, c1564, c56, c1678, c1671, c263, c245, c125, c199, c1330, c181, c127, c112, c249, c64, c982, c360, c1235] c1679 unsat1679 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c1678 := derived1678 a h
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c1330 := derived1330 a h
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c982 := derived982 a h
  have h16 : Entails.eval a c360 := h 359 (by decide)
  have h17 : Entails.eval a c1235 := derived1235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1680 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1678, some c1671, some c56, some c1679, some c2, some c197, some c125, some c265, some c247, some c31, some c112, some c64, some c359, some c360, some c1235, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1680 : lratChecker f1680 p1680 = .success := by decide +kernel
theorem unsat1680 : Unsatisfiable (PosFin 57) f1680 := by
  apply lratCheckerSound f1680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1680
  · intro a ha; simp [p1680] at ha; subst a; trivial
  · exact checked1680
theorem derived1680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1680 := by
  apply localUnsat_implies_entails f1680 [c1635, c1564, c1678, c1671, c56, c1679, c2, c197, c125, c265, c247, c31, c112, c64, c359, c360, c1235] c1680 unsat1680 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1678 := derived1678 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c1679 := derived1679 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c1235 := derived1235 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1681 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1677, some c1671, some c1678, some c1680, some c151, some c1652, some c354, some c2, some c221, some c263, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c1677, c1671, c1678, c1680, c151, c1652, c354, c2, c221, c263] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c1677 := derived1677 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1678 := derived1678 a h
  have h3 : Entails.eval a c1680 := derived1680 a h
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c1652 := derived1652 a h
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c221 := h 220 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1677, some c1671, some c1681, some c262, some c1357, some c2, some c21, some c111, some c151, some c1230, some c1231, some c360, some c179, some c64, some c112, some c1242, some c31, some c525, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1564, c1677, c1671, c1681, c262, c1357, c2, c21, c111, c151, c1230, c1231, c360, c179, c64, c112, c1242, c31, c525] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1677 := derived1677 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1681 := derived1681 a h
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c1357 := derived1357 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c1230 := derived1230 a h
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c1242 := derived1242 a h
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c525 := derived525 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1682, some c1677, some c1671, some c56, some c1663, some c111, some c1232, some c181, some c247, some c4, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c1564, c1682, c1677, c1671, c56, c1663, c111, c1232, c181, c247, c4] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1682 := derived1682 a h
  have h2 : Entails.eval a c1677 := derived1677 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c1663 := derived1663 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1232 := derived1232 a h
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1684 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1683, some c1682, some c1671, some c151, some c354, some c2, some c23, some c263, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1683, c1682, c1671, c151, c354, c2, c23, c263] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1683 := derived1683 a h
  have h1 : Entails.eval a c1682 := derived1682 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c151 := h 150 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1684, some c21, some c1678, some c262, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c1684, c21, c1678, c262] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c1684 := derived1684 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c1678 := derived1678 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1677, some c1685, some c108, some c1231, some c1671, some c263, some c245, some c1620, some c125, some c1158, some c199, some c221, some c127, some c982, some c249, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c1564, c1635, c1677, c1685, c108, c1231, c1671, c263, c245, c1620, c125, c1158, c199, c221, c127, c982, c249] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1677 := derived1677 a h
  have h3 : Entails.eval a c1685 := derived1685 a h
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c1620 := derived1620 a h
  have h10 : Entails.eval a c125 := h 124 (by decide)
  have h11 : Entails.eval a c1158 := derived1158 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c982 := derived982 a h
  have h16 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c115, some c1685, some c1141, some c1677, some c1671, some c64, some c1686, some c114, some c197, some c125, some c265, some c1183, some c127, some c209, some c164, some c200, some c285, some c18, some c149, some c48, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1564, c1635, c115, c1685, c1141, c1677, c1671, c64, c1686, c114, c197, c125, c265, c1183, c127, c209, c164, c200, c285, c18, c149, c48] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1685 := derived1685 a h
  have h4 : Entails.eval a c1141 := derived1141 a h
  have h5 : Entails.eval a c1677 := derived1677 a h
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c1686 := derived1686 a h
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c1183 := derived1183 a h
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c164 := h 163 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c285 := h 284 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c149 := h 148 (by decide)
  have h21 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨33, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1671, some c125, some c199, some c153, some c127, some c221, some c266, some c355, some c224, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c1635, c1671, c125, c199, c153, c127, c221, c266, c355, c224] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1689 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1671, some c1688, some c265, some c1183, some c127, some c155, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c1635, c1671, c1688, c265, c1183, c127, c155] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1688 := derived1688 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c1183 := derived1183 a h
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1677, some c1685, some c108, some c1231, some c1671, some c1232, some c181, some c247, some c4, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c1564, c1677, c1685, c108, c1231, c1671, c1232, c181, c247, c4] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1677 := derived1677 a h
  have h2 : Entails.eval a c1685 := derived1685 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1232 := derived1232 a h
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1685, some c1690, some c109, some c1689, some c1687, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c1685, c1690, c109, c1689, c1687] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c1685 := derived1685 a h
  have h1 : Entails.eval a c1690 := derived1690 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1689 := derived1689 a h
  have h4 : Entails.eval a c1687 := derived1687 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1685, some c1690, some c109, some c1677, some c108, some c1230, some c1671, some c1141, some c1691, some c360, some c64, some c151, some c1688, some c114, some c263, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1635, c1564, c1685, c1690, c109, c1677, c108, c1230, c1671, c1141, c1691, c360, c64, c151, c1688, c114, c263] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1685 := derived1685 a h
  have h3 : Entails.eval a c1690 := derived1690 a h
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c1677 := derived1677 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1230 := derived1230 a h
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c1141 := derived1141 a h
  have h10 : Entails.eval a c1691 := derived1691 a h
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c1688 := derived1688 a h
  have h15 : Entails.eval a c114 := h 113 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1693 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨20, by decide⟩, true), (⟨38, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1692, some c264, some c1690, some c1677, some c1685, some c108, some c1231, some c1230, some c1671, some c181, some c387, some c116, some c128, some c1233, some c45, some c200, some c167, some c51, some c1079, some c150, some c288, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1564, c1692, c264, c1690, c1677, c1685, c108, c1231, c1230, c1671, c181, c387, c116, c128, c1233, c45, c200, c167, c51, c1079, c150, c288] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1692 := derived1692 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1690 := derived1690 a h
  have h4 : Entails.eval a c1677 := derived1677 a h
  have h5 : Entails.eval a c1685 := derived1685 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c1230 := derived1230 a h
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c1233 := derived1233 a h
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c1079 := derived1079 a h
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1693

end CochromaticTwenty.Certificates.B16_0_0
