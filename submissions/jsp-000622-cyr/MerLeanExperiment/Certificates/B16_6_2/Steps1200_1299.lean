import MerLeanExperiment.Certificates.B16_6_2.Steps1100_1199

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1593 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1591, some c1592, some c1590, some c323, some c321, some c1221, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1593 : lratChecker f1593 p1593 = .success := by decide +kernel
theorem unsat1593 : Unsatisfiable (PosFin 57) f1593 := by
  apply lratCheckerSound f1593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1593
  · intro a ha; simp [p1593] at ha; subst a; trivial
  · exact checked1593
theorem derived1593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1593 := by
  apply localUnsat_implies_entails f1593 [c1585, c1591, c1592, c1590, c323, c321, c1221] c1593 unsat1593 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1591 := derived1591 a h
  have h2 : Entails.eval a c1592 := derived1592 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1221 := derived1221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1594 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1287, some c385, some c1593, some c1509, some c1589, some c78, some c92, some c1555, some c112, some c96, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 57) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c1585, c1287, c385, c1593, c1509, c1589, c78, c92, c1555, c112, c96] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c1593 := derived1593 a h
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c1589 := derived1589 a h
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c1555 := derived1555 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c146, some c345, some c15, some c1217, some c1218, some c167, some c207, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 57) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c314, c146, c345, c15, c1217, c1218, c167, c207] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c1217 := derived1217 a h
  have h5 : Entails.eval a c1218 := derived1218 a h
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1593, some c1594, some c1530, some c41, some c1151, some c1585, some c1287, some c385, some c1509, some c300, some c74, some c54, some c81, some c85, some c284, some c112, some c37, some c1214, some c328, some c1595, some c347, some c226, some c31, some c254, some c128, some c113, some c176, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 57) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c1489, c1593, c1594, c1530, c41, c1151, c1585, c1287, c385, c1509, c300, c74, c54, c81, c85, c284, c112, c37, c1214, c328, c1595, c347, c226, c31, c254, c128, c113, c176] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1593 := derived1593 a h
  have h2 : Entails.eval a c1594 := derived1594 a h
  have h3 : Entails.eval a c1530 := derived1530 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1151 := derived1151 a h
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c385 := h 384 (by decide)
  have h9 : Entails.eval a c1509 := derived1509 a h
  have h10 : Entails.eval a c300 := h 299 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c1214 := derived1214 a h
  have h19 : Entails.eval a c328 := h 327 (by decide)
  have h20 : Entails.eval a c1595 := derived1595 a h
  have h21 : Entails.eval a c347 := h 346 (by decide)
  have h22 : Entails.eval a c226 := h 225 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c254 := h 253 (by decide)
  have h25 : Entails.eval a c128 := h 127 (by decide)
  have h26 : Entails.eval a c113 := h 112 (by decide)
  have h27 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1593, some c1585, some c1287, some c41, some c1151, some c1594, some c1596, some c1210, some c1215, some c1220, some c15, some c324, some c146, some c118, some c1219, some c31, some c254, some c215, some c113, some c263, some c176, some c227, some c53, some c343, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 57) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c1489, c1593, c1585, c1287, c41, c1151, c1594, c1596, c1210, c1215, c1220, c15, c324, c146, c118, c1219, c31, c254, c215, c113, c263, c176, c227, c53, c343] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1593 := derived1593 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c1151 := derived1151 a h
  have h6 : Entails.eval a c1594 := derived1594 a h
  have h7 : Entails.eval a c1596 := derived1596 a h
  have h8 : Entails.eval a c1210 := derived1210 a h
  have h9 : Entails.eval a c1215 := derived1215 a h
  have h10 : Entails.eval a c1220 := derived1220 a h
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c1219 := derived1219 a h
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c227 := h 226 (by decide)
  have h23 : Entails.eval a c53 := h 52 (by decide)
  have h24 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1593, some c1597, some c323, some c321, some c1220, some c1221, some c392, some c385, some c1219, some c1148, some c324, some c1506, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 57) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1489, c1585, c1593, c1597, c323, c321, c1220, c1221, c392, c385, c1219, c1148, c324, c1506] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1593 := derived1593 a h
  have h3 : Entails.eval a c1597 := derived1597 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1220 := derived1220 a h
  have h7 : Entails.eval a c1221 := derived1221 a h
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c1219 := derived1219 a h
  have h11 : Entails.eval a c1148 := derived1148 a h
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c1506 := derived1506 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1287, some c385, some c1224, some c1311, some c1304, some c383, some c59, some c1222, some c292, some c351, some c335, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 57) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1585, c1287, c385, c1224, c1311, c1304, c383, c59, c1222, c292, c351, c335] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c1224 := derived1224 a h
  have h4 : Entails.eval a c1311 := derived1311 a h
  have h5 : Entails.eval a c1304 := derived1304 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c1222 := derived1222 a h
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1600 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1585, some c1598, some c1223, some c1599, some c323, some c321, some c1221, some c392, some c1222, some c1219, some c1136, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 57) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1585, c1598, c1223, c1599, c323, c321, c1221, c392, c1222, c1219, c1136] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1585 := derived1585 a h
  have h1 : Entails.eval a c1598 := derived1598 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c1599 := derived1599 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c1222 := derived1222 a h
  have h9 : Entails.eval a c1219 := derived1219 a h
  have h10 : Entails.eval a c1136 := derived1136 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c308, some c379, some c1215, some c73, some c53, some c188, some c385, some c343, some c127, some c1221, some c255, some c321, some c328, some c210, some c1219, some c263, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 57) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1489, c1585, c308, c379, c1215, c73, c53, c188, c385, c343, c127, c1221, c255, c321, c328, c210, c1219, c263] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c1215 := derived1215 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c385 := h 384 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c1221 := derived1221 a h
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c1219 := derived1219 a h
  have h17 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1600, some c1601, some c1223, some c1211, some c1585, some c1287, some c385, some c490, some c1577, some c1224, some c111, some c377, some c36, some c1061, some c110, some c41, some c81, some c298, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 57) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c1489, c1600, c1601, c1223, c1211, c1585, c1287, c385, c490, c1577, c1224, c111, c377, c36, c1061, c110, c41, c81, c298] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1600 := derived1600 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c1223 := derived1223 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1585 := derived1585 a h
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c490 := derived490 a h
  have h9 : Entails.eval a c1577 := derived1577 a h
  have h10 : Entails.eval a c1224 := derived1224 a h
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c1061 := derived1061 a h
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1600, some c1602, some c323, some c321, some c295, some c1221, some c73, some c385, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 57) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1489, c1585, c1600, c1602, c323, c321, c295, c1221, c73, c385] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1600 := derived1600 a h
  have h3 : Entails.eval a c1602 := derived1602 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c1221 := derived1221 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨36, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c42, some c62, some c328, some c287, some c145, some c37, some c312, some c14, some c281, some c1135, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 57) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1489, c1585, c1287, c385, c42, c62, c328, c287, c145, c37, c312, c14, c281, c1135] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c312 := h 311 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c281 := h 280 (by decide)
  have h13 : Entails.eval a c1135 := derived1135 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1605 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c1603, some c1586, some c1587, some c389, some c53, some c378, some c1579, some c92, some c58, some c353, some c1604, some c112, some c108, some c96, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 57) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c1489, c1585, c1287, c385, c1603, c1586, c1587, c389, c53, c378, c1579, c92, c58, c353, c1604, c112, c108, c96] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1603 := derived1603 a h
  have h5 : Entails.eval a c1586 := derived1586 a h
  have h6 : Entails.eval a c1587 := derived1587 a h
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c1579 := derived1579 a h
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c1604 := derived1604 a h
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c1603, some c42, some c1212, some c328, some c324, some c388, some c312, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 57) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1489, c1585, c1287, c385, c1603, c42, c1212, c328, c324, c388, c312] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1603 := derived1603 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c1212 := derived1212 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨46, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1603, some c328, some c324, some c301, some c287, some c312, some c334, some c389, some c289, some c318, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 57) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1603, c328, c324, c301, c287, c312, c334, c389, c289, c318] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1603 := derived1603 a h
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨46, by decide⟩, true), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1603, some c304, some c290, some c338, some c374, some c353, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 57) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1603, c304, c290, c338, c374, c353] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1603 := derived1603 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1605, some c1585, some c1287, some c385, some c110, some c109, some c1214, some c43, some c1606, some c112, some c88, some c59, some c343, some c292, some c53, some c63, some c378, some c1607, some c1608, some c145, some c10, some c143, some c150, some c351, some c176, some c167, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 57) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1489, c1605, c1585, c1287, c385, c110, c109, c1214, c43, c1606, c112, c88, c59, c343, c292, c53, c63, c378, c1607, c1608, c145, c10, c143, c150, c351, c176, c167] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1605 := derived1605 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1214 := derived1214 a h
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c1606 := derived1606 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c378 := h 377 (by decide)
  have h18 : Entails.eval a c1607 := derived1607 a h
  have h19 : Entails.eval a c1608 := derived1608 a h
  have h20 : Entails.eval a c145 := h 144 (by decide)
  have h21 : Entails.eval a c10 := h 9 (by decide)
  have h22 : Entails.eval a c143 := h 142 (by decide)
  have h23 : Entails.eval a c150 := h 149 (by decide)
  have h24 : Entails.eval a c351 := h 350 (by decide)
  have h25 : Entails.eval a c176 := h 175 (by decide)
  have h26 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1610 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c1603, some c1609, some c41, some c326, some c300, some c74, some c389, some c388, some c318, some c314, some c328, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 57) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1489, c1585, c1287, c385, c1603, c1609, c41, c326, c300, c74, c389, c388, c318, c314, c328] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1603 := derived1603 a h
  have h5 : Entails.eval a c1609 := derived1609 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c326 := h 325 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c314 := h 313 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨25, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c388, some c1287, some c110, some c8, some c108, some c1511, some c1323, some c142, some c43, some c1579, some c10, some c187, some c465, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 57) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1489, c388, c1287, c110, c8, c108, c1511, c1323, c142, c43, c1579, c10, c187, c465] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1511 := derived1511 a h
  have h7 : Entails.eval a c1323 := derived1323 a h
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c1579 := derived1579 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c187 := h 186 (by decide)
  have h13 : Entails.eval a c465 := derived465 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1287, some c385, some c1603, some c1610, some c1210, some c1215, some c1221, some c328, some c42, some c1219, some c388, some c1611, some c41, some c74, some c96, some c111, some c112, some c43, some c88, some c298, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 57) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c1489, c1585, c1287, c385, c1603, c1610, c1210, c1215, c1221, c328, c42, c1219, c388, c1611, c41, c74, c96, c111, c112, c43, c88, c298] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1603 := derived1603 a h
  have h5 : Entails.eval a c1610 := derived1610 a h
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1221 := derived1221 a h
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c1219 := derived1219 a h
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c1611 := derived1611 a h
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c43 := h 42 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1613 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1603, some c1585, some c1287, some c385, some c1612, some c1599, some c1577, some c1311, some c1315, some c1304, some c88, some c59, some c108, some c343, some c292, some c61, some c337, some c346, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1613 : lratChecker f1613 p1613 = .success := by decide +kernel
theorem unsat1613 : Unsatisfiable (PosFin 57) f1613 := by
  apply lratCheckerSound f1613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1613
  · intro a ha; simp [p1613] at ha; subst a; trivial
  · exact checked1613
theorem derived1613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1613 := by
  apply localUnsat_implies_entails f1613 [c1489, c1603, c1585, c1287, c385, c1612, c1599, c1577, c1311, c1315, c1304, c88, c59, c108, c343, c292, c61, c337, c346] c1613 unsat1613 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1603 := derived1603 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c1612 := derived1612 a h
  have h6 : Entails.eval a c1599 := derived1599 a h
  have h7 : Entails.eval a c1577 := derived1577 a h
  have h8 : Entails.eval a c1311 := derived1311 a h
  have h9 : Entails.eval a c1315 := derived1315 a h
  have h10 : Entails.eval a c1304 := derived1304 a h
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1614 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨49, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c73, some c176, some c378, some c110, some c8, some c78, some c189, some c389, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1614 : lratChecker f1614 p1614 = .success := by decide +kernel
theorem unsat1614 : Unsatisfiable (PosFin 57) f1614 := by
  apply lratCheckerSound f1614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1614
  · intro a ha; simp [p1614] at ha; subst a; trivial
  · exact checked1614
theorem derived1614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1614 := by
  apply localUnsat_implies_entails f1614 [c1489, c73, c176, c378, c110, c8, c78, c189, c389] c1614 unsat1614 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1615 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1585, some c1613, some c323, some c321, some c1221, some c385, some c73, some c392, some c1219, some c1215, some c1210, some c1603, some c378, some c176, some c190, some c1614, some c93, some c389, some c370, some c78, some c599, some c611, some c266, some c264, some c252, some c248, some c31, some c301, some c217, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1615 : lratChecker f1615 p1615 = .success := by decide +kernel
theorem unsat1615 : Unsatisfiable (PosFin 57) f1615 := by
  apply lratCheckerSound f1615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1615
  · intro a ha; simp [p1615] at ha; subst a; trivial
  · exact checked1615
theorem derived1615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1615 := by
  apply localUnsat_implies_entails f1615 [c1489, c1585, c1613, c323, c321, c1221, c385, c73, c392, c1219, c1215, c1210, c1603, c378, c176, c190, c1614, c93, c389, c370, c78, c599, c611, c266, c264, c252, c248, c31, c301, c217] c1615 unsat1615 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1585 := derived1585 a h
  have h2 : Entails.eval a c1613 := derived1613 a h
  have h3 : Entails.eval a c323 := h 322 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c1221 := derived1221 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c1219 := derived1219 a h
  have h10 : Entails.eval a c1215 := derived1215 a h
  have h11 : Entails.eval a c1210 := derived1210 a h
  have h12 : Entails.eval a c1603 := derived1603 a h
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c1614 := derived1614 a h
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c389 := h 388 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c599 := derived599 a h
  have h22 : Entails.eval a c611 := derived611 a h
  have h23 : Entails.eval a c266 := h 265 (by decide)
  have h24 : Entails.eval a c264 := h 263 (by decide)
  have h25 : Entails.eval a c252 := h 251 (by decide)
  have h26 : Entails.eval a c248 := h 247 (by decide)
  have h27 : Entails.eval a c31 := h 30 (by decide)
  have h28 : Entails.eval a c301 := h 300 (by decide)
  have h29 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1616 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c38, some c294, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1616 : lratChecker f1616 p1616 = .success := by decide +kernel
theorem unsat1616 : Unsatisfiable (PosFin 57) f1616 := by
  apply lratCheckerSound f1616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1616
  · intro a ha; simp [p1616] at ha; subst a; trivial
  · exact checked1616
theorem derived1616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1616 := by
  apply localUnsat_implies_entails f1616 [c78, c38, c294] c1616 unsat1616 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1617 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true), (⟨51, by decide⟩, true), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c73, some c1616, some c389, some c94, some c108, some c92, some c58, some c1549, some c112, some c868, some c50, some c278, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1617 : lratChecker f1617 p1617 = .success := by decide +kernel
theorem unsat1617 : Unsatisfiable (PosFin 57) f1617 := by
  apply lratCheckerSound f1617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1617
  · intro a ha; simp [p1617] at ha; subst a; trivial
  · exact checked1617
theorem derived1617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1617 := by
  apply localUnsat_implies_entails f1617 [c1489, c73, c1616, c389, c94, c108, c92, c58, c1549, c112, c868, c50, c278] c1617 unsat1617 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c1616 := derived1616 a h
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c1549 := derived1549 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c868 := derived868 a h
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1618 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1615, some c1585, some c1613, some c323, some c321, some c1221, some c385, some c73, some c392, some c1219, some c1215, some c1210, some c1603, some c110, some c8, some c1616, some c389, some c477, some c189, some c203, some c1617, some c294, some c1122, some c118, some c1138, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1618 : lratChecker f1618 p1618 = .success := by decide +kernel
theorem unsat1618 : Unsatisfiable (PosFin 57) f1618 := by
  apply lratCheckerSound f1618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1618
  · intro a ha; simp [p1618] at ha; subst a; trivial
  · exact checked1618
theorem derived1618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1618 := by
  apply localUnsat_implies_entails f1618 [c1489, c1615, c1585, c1613, c323, c321, c1221, c385, c73, c392, c1219, c1215, c1210, c1603, c110, c8, c1616, c389, c477, c189, c203, c1617, c294, c1122, c118, c1138] c1618 unsat1618 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1615 := derived1615 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c1219 := derived1219 a h
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1210 := derived1210 a h
  have h13 : Entails.eval a c1603 := derived1603 a h
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c1616 := derived1616 a h
  have h17 : Entails.eval a c389 := h 388 (by decide)
  have h18 : Entails.eval a c477 := derived477 a h
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c1617 := derived1617 a h
  have h22 : Entails.eval a c294 := h 293 (by decide)
  have h23 : Entails.eval a c1122 := derived1122 a h
  have h24 : Entails.eval a c118 := h 117 (by decide)
  have h25 : Entails.eval a c1138 := derived1138 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1619 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1603, some c1585, some c1613, some c323, some c321, some c1210, some c1215, some c1221, some c392, some c385, some c1219, some c73, some c1615, some c1222, some c1618, some c93, some c389, some c1616, some c15, some c146, some c194, some c575, some c599, some c611, some c266, some c264, some c252, some c248, some c31, some c301, some c217, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 57) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c1489, c1603, c1585, c1613, c323, c321, c1210, c1215, c1221, c392, c385, c1219, c73, c1615, c1222, c1618, c93, c389, c1616, c15, c146, c194, c575, c599, c611, c266, c264, c252, c248, c31, c301, c217] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1603 := derived1603 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1221 := derived1221 a h
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c1219 := derived1219 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c1615 := derived1615 a h
  have h14 : Entails.eval a c1222 := derived1222 a h
  have h15 : Entails.eval a c1618 := derived1618 a h
  have h16 : Entails.eval a c93 := h 92 (by decide)
  have h17 : Entails.eval a c389 := h 388 (by decide)
  have h18 : Entails.eval a c1616 := derived1616 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c146 := h 145 (by decide)
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c575 := derived575 a h
  have h23 : Entails.eval a c599 := derived599 a h
  have h24 : Entails.eval a c611 := derived611 a h
  have h25 : Entails.eval a c266 := h 265 (by decide)
  have h26 : Entails.eval a c264 := h 263 (by decide)
  have h27 : Entails.eval a c252 := h 251 (by decide)
  have h28 : Entails.eval a c248 := h 247 (by decide)
  have h29 : Entails.eval a c31 := h 30 (by decide)
  have h30 : Entails.eval a c301 := h 300 (by decide)
  have h31 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1620 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1619, some c1601, some c1585, some c392, some c385, some c1222, some c1134, some c303, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 57) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c1619, c1601, c1585, c392, c385, c1222, c1134, c303] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c1619 := derived1619 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c392 := h 391 (by decide)
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c1134 := derived1134 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1603, some c1619, some c1601, some c1620, some c1224, some c306, some c384, some c1221, some c1222, some c323, some c388, some c1315, some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 57) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c1603, c1619, c1601, c1620, c1224, c306, c384, c1221, c1222, c323, c388, c1315] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c1603 := derived1603 a h
  have h1 : Entails.eval a c1619 := derived1619 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c1620 := derived1620 a h
  have h4 : Entails.eval a c1224 := derived1224 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c1221 := derived1221 a h
  have h8 : Entails.eval a c1222 := derived1222 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c1315 := derived1315 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨30, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1592, some c1287, some c316, some c147, some c39, some c42, some c1574, some c11, some c108, some c1543, some c154, some c1213, some c185, some c1062, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 57) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1621, c1489, c1592, c1287, c316, c147, c39, c42, c1574, c11, c108, c1543, c154, c1213, c185, c1062] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1592 := derived1592 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c1574 := derived1574 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c1543 := derived1543 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c1213 := derived1213 a h
  have h14 : Entails.eval a c185 := h 184 (by decide)
  have h15 : Entails.eval a c1062 := derived1062 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1287, some c39, some c147, some c1173, some c316, some c1592, some c1586, some c1179, some c1622, some c327, some c324, some c50, some c1174, some c220, some c218, some c30, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 57) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c1621, c1287, c39, c147, c1173, c316, c1592, c1586, c1179, c1622, c327, c324, c50, c1174, c220, c218, c30] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c1173 := derived1173 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c1592 := derived1592 a h
  have h7 : Entails.eval a c1586 := derived1586 a h
  have h8 : Entails.eval a c1179 := derived1179 a h
  have h9 : Entails.eval a c1622 := derived1622 a h
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c1174 := derived1174 a h
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c39, some c147, some c1173, some c316, some c372, some c1287, some c1623, some c1509, some c41, some c376, some c300, some c324, some c74, some c54, some c42, some c347, some c11, some c226, some c150, some c115, some c254, some c259, some c27, some c1102, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 57) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1621, c1489, c39, c147, c1173, c316, c372, c1287, c1623, c1509, c41, c376, c300, c324, c74, c54, c42, c347, c11, c226, c150, c115, c254, c259, c27, c1102] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c1173 := derived1173 a h
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c1623 := derived1623 a h
  have h9 : Entails.eval a c1509 := derived1509 a h
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c226 := h 225 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  have h21 : Entails.eval a c115 := h 114 (by decide)
  have h22 : Entails.eval a c254 := h 253 (by decide)
  have h23 : Entails.eval a c259 := h 258 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  have h25 : Entails.eval a c1102 := derived1102 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨38, by decide⟩, true), (⟨37, by decide⟩, true), (⟨30, by decide⟩, true), (⟨41, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c316, some c70, some c1574, some c46, some c82, some c301, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 57) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1621, c1489, c316, c70, c1574, c46, c82, c301] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c316 := h 315 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c1574 := derived1574 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c39, some c147, some c372, some c316, some c1173, some c1624, some c296, some c974, some c322, some c73, some c53, some c341, some c342, some c1625, some c1592, some c1509, some c81, some c338, some c300, some c380, some c304, some c44, some c82, some c1574, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 57) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1621, c1489, c39, c147, c372, c316, c1173, c1624, c296, c974, c322, c73, c53, c341, c342, c1625, c1592, c1509, c81, c338, c300, c380, c304, c44, c82, c1574] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c1173 := derived1173 a h
  have h7 : Entails.eval a c1624 := derived1624 a h
  have h8 : Entails.eval a c296 := h 295 (by decide)
  have h9 : Entails.eval a c974 := derived974 a h
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c1625 := derived1625 a h
  have h16 : Entails.eval a c1592 := derived1592 a h
  have h17 : Entails.eval a c1509 := derived1509 a h
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c300 := h 299 (by decide)
  have h21 : Entails.eval a c380 := h 379 (by decide)
  have h22 : Entails.eval a c304 := h 303 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  have h24 : Entails.eval a c82 := h 81 (by decide)
  have h25 : Entails.eval a c1574 := derived1574 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1626, some c392, some c385, some c1591, some c1287, some c73, some c1148, some c296, some c1220, some c1219, some c327, some c324, some c44, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 57) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1489, c1626, c392, c385, c1591, c1287, c73, c1148, c296, c1220, c1219, c327, c324, c44] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1626 := derived1626 a h
  have h2 : Entails.eval a c392 := h 391 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1591 := derived1591 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c1148 := derived1148 a h
  have h8 : Entails.eval a c296 := h 295 (by decide)
  have h9 : Entails.eval a c1220 := derived1220 a h
  have h10 : Entails.eval a c1219 := derived1219 a h
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1592, some c1287, some c316, some c42, some c1622, some c1574, some c108, some c305, some c1543, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 57) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1621, c1489, c1592, c1287, c316, c42, c1622, c1574, c108, c305, c1543] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1592 := derived1592 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c316 := h 315 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c1622 := derived1622 a h
  have h7 : Entails.eval a c1574 := derived1574 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c1543 := derived1543 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1223, some c1211, some c39, some c1062, some c147, some c16, some c1094, some c316, some c1628, some c324, some c301, some c313, some c1052, some c213, some c24, some c257, some c247, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 57) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c1621, c1223, c1211, c39, c1062, c147, c16, c1094, c316, c1628, c324, c301, c313, c1052, c213, c24, c257, c247] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1223 := derived1223 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1062 := derived1062 a h
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c1094 := derived1094 a h
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c1628 := derived1628 a h
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c1052 := derived1052 a h
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1223, some c1211, some c39, some c1062, some c147, some c16, some c1094, some c1173, some c316, some c1629, some c41, some c324, some c298, some c42, some c74, some c54, some c11, some c284, some c345, some c167, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 57) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c1621, c1489, c1223, c1211, c39, c1062, c147, c16, c1094, c1173, c316, c1629, c41, c324, c298, c42, c74, c54, c11, c284, c345, c167] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c1062 := derived1062 a h
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c1094 := derived1094 a h
  have h9 : Entails.eval a c1173 := derived1173 a h
  have h10 : Entails.eval a c316 := h 315 (by decide)
  have h11 : Entails.eval a c1629 := derived1629 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c298 := h 297 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c54 := h 53 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨30, by decide⟩, true), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c316, some c147, some c39, some c327, some c301, some c50, some c1172, some c1574, some c185, some c86, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 57) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c1621, c316, c147, c39, c327, c301, c50, c1172, c1574, c185, c86] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c1172 := derived1172 a h
  have h8 : Entails.eval a c1574 := derived1574 a h
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨30, by decide⟩, true), (⟨12, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c316, some c147, some c39, some c1631, some c46, some c1574, some c11, some c1273, some c154, some c185, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 57) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c1621, c316, c147, c39, c1631, c46, c1574, c11, c1273, c154, c185] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c316 := h 315 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c1631 := derived1631 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c1574 := derived1574 a h
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c1273 := derived1273 a h
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨28, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c39, some c324, some c301, some c313, some c1052, some c213, some c220, some c259, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 57) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c1621, c39, c324, c301, c313, c1052, c213, c220, c259] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c1052 := derived1052 a h
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c181, some c1532, some c115, some c205, some c257, some c114, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p1634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 57) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c181, c1532, c115, c205, c257, c114] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c181 := h 180 (by decide)
  have h1 : Entails.eval a c1532 := derived1532 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1634, some c1052, some c213, some c220, some c259, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 57) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1621, c1634, c1052, c213, c220, c259] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1634 := derived1634 a h
  have h2 : Entails.eval a c1052 := derived1052 a h
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c220 := h 219 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1636 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨32, by decide⟩, false), (⟨12, by decide⟩, false), (⟨28, by decide⟩, false), (⟨7, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1211, some c1635, some c298, some c54, some c284, some c347, some c228, some c226, some c31, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 57) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c1211, c1635, c298, c54, c284, c347, c228, c226, c31] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c1211 := derived1211 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c347 := h 346 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨28, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c313, some c369, some c298, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 57) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c1621, c313, c369, c298] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1223, some c1211, some c39, some c147, some c316, some c1062, some c1173, some c16, some c1094, some c1630, some c974, some c322, some c1632, some c1592, some c1633, some c1637, some c1635, some c1636, some c298, some c185, some c54, some c1532, some c284, some c345, some c335, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 57) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c1621, c1223, c1211, c39, c147, c316, c1062, c1173, c16, c1094, c1630, c974, c322, c1632, c1592, c1633, c1637, c1635, c1636, c298, c185, c54, c1532, c284, c345, c335] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1223 := derived1223 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c1062 := derived1062 a h
  have h7 : Entails.eval a c1173 := derived1173 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c1094 := derived1094 a h
  have h10 : Entails.eval a c1630 := derived1630 a h
  have h11 : Entails.eval a c974 := derived974 a h
  have h12 : Entails.eval a c322 := h 321 (by decide)
  have h13 : Entails.eval a c1632 := derived1632 a h
  have h14 : Entails.eval a c1592 := derived1592 a h
  have h15 : Entails.eval a c1633 := derived1633 a h
  have h16 : Entails.eval a c1637 := derived1637 a h
  have h17 : Entails.eval a c1635 := derived1635 a h
  have h18 : Entails.eval a c1636 := derived1636 a h
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c185 := h 184 (by decide)
  have h21 : Entails.eval a c54 := h 53 (by decide)
  have h22 : Entails.eval a c1532 := derived1532 a h
  have h23 : Entails.eval a c284 := h 283 (by decide)
  have h24 : Entails.eval a c345 := h 344 (by decide)
  have h25 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1627, some c1223, some c1638, some c392, some c385, some c1591, some c1222, some c1148, some c380, some c383, some c84, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 57) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1489, c1627, c1223, c1638, c392, c385, c1591, c1222, c1148, c380, c383, c84] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1627 := derived1627 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  have h3 : Entails.eval a c1638 := derived1638 a h
  have h4 : Entails.eval a c392 := h 391 (by decide)
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c1591 := derived1591 a h
  have h7 : Entails.eval a c1222 := derived1222 a h
  have h8 : Entails.eval a c1148 := derived1148 a h
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c39, some c147, some c1173, some c320, some c376, some c307, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 57) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c1621, c39, c147, c1173, c320, c376, c307] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c39, some c147, some c1173, some c1640, some c389, some c313, some c369, some c300, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 57) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1621, c39, c147, c1173, c1640, c389, c313, c369, c300] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c1640 := derived1640 a h
  have h5 : Entails.eval a c389 := h 388 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c383, some c301, some c181, some c607, some c116, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 57) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c380, c383, c301, c181, c607, c116] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c607 := derived607 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c327, some c324, some c45, some c44, some c112, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 57) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c1621, c327, c324, c45, c44, c112] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨28, by decide⟩, true), (⟨44, by decide⟩, true), (⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c391, some c385, some c94, some c119, some c156, some c266, some c9, some c207, some c125, some c56, some c352, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 57) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c1489, c1621, c391, c385, c94, c119, c156, c266, c9, c207, c125, c56, c352] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c125 := h 124 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1639, some c391, some c1641, some c385, some c1287, some c94, some c73, some c296, some c378, some c1210, some c1215, some c1219, some c176, some c1614, some c190, some c93, some c389, some c370, some c1642, some c1643, some c1644, some c1173, some c45, some c85, some c297, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 57) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c1489, c1621, c1639, c391, c1641, c385, c1287, c94, c73, c296, c378, c1210, c1215, c1219, c176, c1614, c190, c93, c389, c370, c1642, c1643, c1644, c1173, c45, c85, c297] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c1641 := derived1641 a h
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c1210 := derived1210 a h
  have h12 : Entails.eval a c1215 := derived1215 a h
  have h13 : Entails.eval a c1219 := derived1219 a h
  have h14 : Entails.eval a c176 := h 175 (by decide)
  have h15 : Entails.eval a c1614 := derived1614 a h
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c389 := h 388 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c1642 := derived1642 a h
  have h21 : Entails.eval a c1643 := derived1643 a h
  have h22 : Entails.eval a c1644 := derived1644 a h
  have h23 : Entails.eval a c1173 := derived1173 a h
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c85 := h 84 (by decide)
  have h26 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨27, by decide⟩, false), (⟨55, by decide⟩, true), (⟨43, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c313, some c369, some c297, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 57) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c1621, c313, c369, c297] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1639, some c391, some c1645, some c1222, some c1211, some c39, some c147, some c1173, some c16, some c1216, some c11, some c35, some c1646, some c389, some c1523, some c974, some c320, some c110, some c326, some c41, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 57) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1621, c1489, c1639, c391, c1645, c1222, c1211, c39, c147, c1173, c16, c1216, c11, c35, c1646, c389, c1523, c974, c320, c110, c326, c41] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1639 := derived1639 a h
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c1645 := derived1645 a h
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c1211 := derived1211 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c1173 := derived1173 a h
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c1216 := derived1216 a h
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c1646 := derived1646 a h
  have h15 : Entails.eval a c389 := h 388 (by decide)
  have h16 : Entails.eval a c1523 := derived1523 a h
  have h17 : Entails.eval a c974 := derived974 a h
  have h18 : Entails.eval a c320 := h 319 (by decide)
  have h19 : Entails.eval a c110 := h 109 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1287, some c73, some c1211, some c110, some c1616, some c389, some c94, some c108, some c322, some c1340, some c112, some c1549, some c50, some c868, some c293, some c277, some c57, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 57) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1489, c1287, c73, c1211, c110, c1616, c389, c94, c108, c322, c1340, c112, c1549, c50, c868, c293, c277, c57] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1616 := derived1616 a h
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c322 := h 321 (by decide)
  have h10 : Entails.eval a c1340 := derived1340 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c1549 := derived1549 a h
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c868 := derived868 a h
  have h15 : Entails.eval a c293 := h 292 (by decide)
  have h16 : Entails.eval a c277 := h 276 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1647, some c385, some c73, some c1639, some c391, some c94, some c1287, some c1645, some c1211, some c108, some c110, some c1616, some c389, some c1648, some c1215, some c1219, some c8, some c477, some c189, some c142, some c203, some c324, some c119, some c160, some c48, some c32, some c575, some c1549, some c228, some c868, some c1051, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 57) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c1621, c1489, c1647, c385, c73, c1639, c391, c94, c1287, c1645, c1211, c108, c110, c1616, c389, c1648, c1215, c1219, c8, c477, c189, c142, c203, c324, c119, c160, c48, c32, c575, c1549, c228, c868, c1051] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1647 := derived1647 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c1645 := derived1645 a h
  have h10 : Entails.eval a c1211 := derived1211 a h
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c1616 := derived1616 a h
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c1648 := derived1648 a h
  have h16 : Entails.eval a c1215 := derived1215 a h
  have h17 : Entails.eval a c1219 := derived1219 a h
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c477 := derived477 a h
  have h20 : Entails.eval a c189 := h 188 (by decide)
  have h21 : Entails.eval a c142 := h 141 (by decide)
  have h22 : Entails.eval a c203 := h 202 (by decide)
  have h23 : Entails.eval a c324 := h 323 (by decide)
  have h24 : Entails.eval a c119 := h 118 (by decide)
  have h25 : Entails.eval a c160 := h 159 (by decide)
  have h26 : Entails.eval a c48 := h 47 (by decide)
  have h27 : Entails.eval a c32 := h 31 (by decide)
  have h28 : Entails.eval a c575 := derived575 a h
  have h29 : Entails.eval a c1549 := derived1549 a h
  have h30 : Entails.eval a c228 := h 227 (by decide)
  have h31 : Entails.eval a c868 := derived868 a h
  have h32 : Entails.eval a c1051 := derived1051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1647, some c385, some c1287, some c73, some c1639, some c1649, some c93, some c389, some c1616, some c391, some c94, some c1645, some c1222, some c1211, some c146, some c314, some c15, some c1643, some c1216, some c1642, some c1644, some c11, some c45, some c85, some c297, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 57) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c1489, c1621, c1647, c385, c1287, c73, c1639, c1649, c93, c389, c1616, c391, c94, c1645, c1222, c1211, c146, c314, c15, c1643, c1216, c1642, c1644, c11, c45, c85, c297] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1647 := derived1647 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c1639 := derived1639 a h
  have h7 : Entails.eval a c1649 := derived1649 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c1616 := derived1616 a h
  have h11 : Entails.eval a c391 := h 390 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c1645 := derived1645 a h
  have h14 : Entails.eval a c1222 := derived1222 a h
  have h15 : Entails.eval a c1211 := derived1211 a h
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c1643 := derived1643 a h
  have h20 : Entails.eval a c1216 := derived1216 a h
  have h21 : Entails.eval a c1642 := derived1642 a h
  have h22 : Entails.eval a c1644 := derived1644 a h
  have h23 : Entails.eval a c11 := h 10 (by decide)
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c85 := h 84 (by decide)
  have h26 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1639, some c391, some c1645, some c1211, some c1222, some c1647, some c385, some c1287, some c94, some c73, some c1649, some c93, some c389, some c1616, some c1650, some c322, some c1215, some c1219, some c15, some c1643, some c194, some c1642, some c1644, some c203, some c208, some c1006, some c1121, some c354, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 57) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c1489, c1639, c391, c1645, c1211, c1222, c1647, c385, c1287, c94, c73, c1649, c93, c389, c1616, c1650, c322, c1215, c1219, c15, c1643, c194, c1642, c1644, c203, c208, c1006, c1121, c354] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1639 := derived1639 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c1645 := derived1645 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c1647 := derived1647 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c1649 := derived1649 a h
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c1616 := derived1616 a h
  have h15 : Entails.eval a c1650 := derived1650 a h
  have h16 : Entails.eval a c322 := h 321 (by decide)
  have h17 : Entails.eval a c1215 := derived1215 a h
  have h18 : Entails.eval a c1219 := derived1219 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c1643 := derived1643 a h
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c1642 := derived1642 a h
  have h23 : Entails.eval a c1644 := derived1644 a h
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c208 := h 207 (by decide)
  have h26 : Entails.eval a c1006 := derived1006 a h
  have h27 : Entails.eval a c1121 := derived1121 a h
  have h28 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨55, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c147, some c39, some c145, some c37, some c14, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 57) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c1621, c147, c39, c145, c37, c14] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1653 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c39, some c147, some c1173, some c1592, some c1628, some c322, some c46, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 57) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c1621, c39, c147, c1173, c1592, c1628, c322, c46] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c1592 := derived1592 a h
  have h5 : Entails.eval a c1628 := derived1628 a h
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1654 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1651, some c39, some c147, some c372, some c316, some c1638, some c1173, some c1652, some c327, some c304, some c77, some c1574, some c1653, some c42, some c296, some c81, some c82, some c380, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 57) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1621, c1489, c1651, c39, c147, c372, c316, c1638, c1173, c1652, c327, c304, c77, c1574, c1653, c42, c296, c81, c82, c380] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1651 := derived1651 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c1638 := derived1638 a h
  have h8 : Entails.eval a c1173 := derived1173 a h
  have h9 : Entails.eval a c1652 := derived1652 a h
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c1574 := derived1574 a h
  have h14 : Entails.eval a c1653 := derived1653 a h
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  have h19 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1287, some c327, some c324, some c145, some c37, some c112, some c14, some c62, some c86, some c119, some c285, some c301, some c255, some c224, some c63, some c209, some c22, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 57) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1621, c1489, c1287, c327, c324, c145, c37, c112, c14, c62, c86, c119, c285, c301, c255, c224, c63, c209, c22] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c301 := h 300 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c224 := h 223 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1316, some c347, some c302, some c286, some c77, some c164, some c12, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 57) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1489, c1316, c347, c302, c286, c77, c164, c12] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1316 := derived1316 a h
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c286 := h 285 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨53, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1656, some c192, some c12, some c37, some c77, some c302, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 57) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1656, c192, c12, c37, c77, c302] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1656 := derived1656 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨46, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1592, some c58, some c1655, some c144, some c36, some c108, some c6, some c62, some c86, some c1657, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 57) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c1489, c1592, c58, c1655, c144, c36, c108, c6, c62, c86, c1657] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1592 := derived1592 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c1655 := derived1655 a h
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c1657 := derived1657 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1592, some c1586, some c1654, some c1651, some c1587, some c53, some c378, some c92, some c1658, some c42, some c112, some c1511, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 57) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1489, c1592, c1586, c1654, c1651, c1587, c53, c378, c92, c1658, c42, c112, c1511] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1592 := derived1592 a h
  have h2 : Entails.eval a c1586 := derived1586 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1651 := derived1651 a h
  have h5 : Entails.eval a c1587 := derived1587 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c1658 := derived1658 a h
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c1511 := derived1511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c145, some c37, some c14, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 57) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c145, c37, c14] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1592, some c1654, some c1651, some c1586, some c1659, some c296, some c1340, some c73, some c53, some c343, some c342, some c227, some c1040, some c1660, some c277, some c70, some c30, some c14, some c125, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 57) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c1489, c1592, c1654, c1651, c1586, c1659, c296, c1340, c73, c53, c343, c342, c227, c1040, c1660, c277, c70, c30, c14, c125] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1592 := derived1592 a h
  have h2 : Entails.eval a c1654 := derived1654 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1586 := derived1586 a h
  have h5 : Entails.eval a c1659 := derived1659 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c1340 := derived1340 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c342 := h 341 (by decide)
  have h12 : Entails.eval a c227 := h 226 (by decide)
  have h13 : Entails.eval a c1040 := derived1040 a h
  have h14 : Entails.eval a c1660 := derived1660 a h
  have h15 : Entails.eval a c277 := h 276 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c30 := h 29 (by decide)
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c42, some c108, some c1511, some c1407, some c112, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 57) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c1489, c1621, c42, c108, c1511, c1407, c112] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1511 := derived1511 a h
  have h5 : Entails.eval a c1407 := derived1407 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1219, some c1210, some c1173, some c119, some c32, some c263, some c215, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 57) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1621, c1219, c1210, c1173, c119, c32, c263, c215] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1219 := derived1219 a h
  have h2 : Entails.eval a c1210 := derived1210 a h
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1592, some c1654, some c1651, some c1661, some c1210, some c1215, some c1220, some c1221, some c8, some c327, some c1219, some c1662, some c1663, some c1407, some c59, some c92, some c52, some c108, some c351, some c575, some c1409, some c62, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 57) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1621, c1489, c1592, c1654, c1651, c1661, c1210, c1215, c1220, c1221, c8, c327, c1219, c1662, c1663, c1407, c59, c92, c52, c108, c351, c575, c1409, c62] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1592 := derived1592 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1651 := derived1651 a h
  have h5 : Entails.eval a c1661 := derived1661 a h
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1220 := derived1220 a h
  have h9 : Entails.eval a c1221 := derived1221 a h
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c1662 := derived1662 a h
  have h14 : Entails.eval a c1663 := derived1663 a h
  have h15 : Entails.eval a c1407 := derived1407 a h
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c92 := h 91 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c108 := h 107 (by decide)
  have h20 : Entails.eval a c351 := h 350 (by decide)
  have h21 : Entails.eval a c575 := derived575 a h
  have h22 : Entails.eval a c1409 := derived1409 a h
  have h23 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1654, some c1651, some c1592, some c1664, some c1223, some c1224, some c1061, some c383, some c108, some c1222, some c55, some c1059, some c351, some c1052, some c227, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 57) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c1489, c1654, c1651, c1592, c1664, c1223, c1224, c1061, c383, c108, c1222, c55, c1059, c351, c1052, c227] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1654 := derived1654 a h
  have h2 : Entails.eval a c1651 := derived1651 a h
  have h3 : Entails.eval a c1592 := derived1592 a h
  have h4 : Entails.eval a c1664 := derived1664 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1061 := derived1061 a h
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c1222 := derived1222 a h
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c1059 := derived1059 a h
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c1052 := derived1052 a h
  have h15 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨49, by decide⟩, false), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1555, some c78, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p1666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 57) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1555, c78] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1555 := derived1555 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1667 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨2, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1509, some c1287, some c41, some c1151, some c300, some c324, some c74, some c144, some c36, some c1171, some c13, some c1666, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 57) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1489, c1509, c1287, c41, c1151, c300, c324, c74, c144, c36, c1171, c13, c1666] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c1151 := derived1151 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c1171 := derived1171 a h
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c1666 := derived1666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, false), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c296, some c73, some c53, some c1023, some c343, some c342, some c340, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 57) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1489, c1621, c296, c73, c53, c1023, c343, c342, c340] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c1023 := derived1023 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨6, by decide⟩, false), (⟨41, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨30, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1287, some c1595, some c347, some c226, some c254, some c31, some c113, some c128, some c176, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 57) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1287, c1595, c347, c226, c254, c31, c113, c128, c176] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1287 := derived1287 a h
  have h1 : Entails.eval a c1595 := derived1595 a h
  have h2 : Entails.eval a c347 := h 346 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c254 := h 253 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1665, some c1509, some c1654, some c1651, some c1668, some c1287, some c41, some c1667, some c1151, some c300, some c42, some c74, some c54, some c81, some c1666, some c284, some c1669, some c85, some c112, some c1214, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 57) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c1489, c1665, c1509, c1654, c1651, c1668, c1287, c41, c1667, c1151, c300, c42, c74, c54, c81, c1666, c284, c1669, c85, c112, c1214] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c1651 := derived1651 a h
  have h5 : Entails.eval a c1668 := derived1668 a h
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c1667 := derived1667 a h
  have h9 : Entails.eval a c1151 := derived1151 a h
  have h10 : Entails.eval a c300 := h 299 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c54 := h 53 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c1666 := derived1666 a h
  have h16 : Entails.eval a c284 := h 283 (by decide)
  have h17 : Entails.eval a c1669 := derived1669 a h
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c1214 := derived1214 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1665, some c1654, some c1651, some c1509, some c1670, some c1210, some c1215, some c1220, some c1221, some c327, some c1219, some c1663, some c45, some c85, some c92, some c1151, some c298, some c15, some c76, some c118, some c29, some c31, some c248, some c215, some c263, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 57) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1621, c1665, c1654, c1651, c1509, c1670, c1210, c1215, c1220, c1221, c327, c1219, c1663, c45, c85, c92, c1151, c298, c15, c76, c118, c29, c31, c248, c215, c263] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1654 := derived1654 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c1670 := derived1670 a h
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c1220 := derived1220 a h
  have h9 : Entails.eval a c1221 := derived1221 a h
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c1219 := derived1219 a h
  have h12 : Entails.eval a c1663 := derived1663 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c1151 := derived1151 a h
  have h17 : Entails.eval a c298 := h 297 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c76 := h 75 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c29 := h 28 (by decide)
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c248 := h 247 (by decide)
  have h24 : Entails.eval a c215 := h 214 (by decide)
  have h25 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1217, some c1218, some c184, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 57) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1217, c1218, c184] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1217 := derived1217 a h
  have h1 : Entails.eval a c1218 := derived1218 a h
  have h2 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1651, some c1671, some c1223, some c1224, some c1672, some c383, some c1211, some c1052, some c16, some c119, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 57) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c1621, c1651, c1671, c1223, c1224, c1672, c383, c1211, c1052, c16, c119] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1223 := derived1223 a h
  have h4 : Entails.eval a c1224 := derived1224 a h
  have h5 : Entails.eval a c1672 := derived1672 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c1211 := derived1211 a h
  have h8 : Entails.eval a c1052 := derived1052 a h
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1674 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1651, some c1665, some c1671, some c1211, some c1223, some c1224, some c1672, some c1673, some c45, some c85, some c1151, some c298, some c52, some c1171, some c15, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1674 : lratChecker f1674 p1674 = .success := by decide +kernel
theorem unsat1674 : Unsatisfiable (PosFin 57) f1674 := by
  apply lratCheckerSound f1674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1674
  · intro a ha; simp [p1674] at ha; subst a; trivial
  · exact checked1674
theorem derived1674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1674 := by
  apply localUnsat_implies_entails f1674 [c1621, c1651, c1665, c1671, c1211, c1223, c1224, c1672, c1673, c45, c85, c1151, c298, c52, c1171, c15] c1674 unsat1674 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1223 := derived1223 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1672 := derived1672 a h
  have h8 : Entails.eval a c1673 := derived1673 a h
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c1151 := derived1151 a h
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c1171 := derived1171 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1675 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨46, by decide⟩, true), (⟨25, by decide⟩, true), (⟨54, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c389, some c1189, some c326, some c291, some c142, some c6, some c8, some c169, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p1675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1675 : lratChecker f1675 p1675 = .success := by decide +kernel
theorem unsat1675 : Unsatisfiable (PosFin 57) f1675 := by
  apply lratCheckerSound f1675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1675
  · intro a ha; simp [p1675] at ha; subst a; trivial
  · exact checked1675
theorem derived1675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1675 := by
  apply localUnsat_implies_entails f1675 [c353, c389, c1189, c326, c291, c142, c6, c8, c169] c1675 unsat1675 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c389 := h 388 (by decide)
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1676 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c380, some c368, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1676 : lratChecker f1676 p1676 = .success := by decide +kernel
theorem unsat1676 : Unsatisfiable (PosFin 57) f1676 := by
  apply lratCheckerSound f1676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1676
  · intro a ha; simp [p1676] at ha; subst a; trivial
  · exact checked1676
theorem derived1676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1676 := by
  apply localUnsat_implies_entails f1676 [c383, c380, c368] c1676 unsat1676 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1677 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1674, some c1586, some c389, some c1641, some c1651, some c1287, some c1587, some c53, some c378, some c1579, some c58, some c108, some c353, some c62, some c86, some c42, some c1675, some c1676, some c224, some c22, some c265, some c220, some c255, some c209, some c229, some c281, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1677 : lratChecker f1677 p1677 = .success := by decide +kernel
theorem unsat1677 : Unsatisfiable (PosFin 57) f1677 := by
  apply lratCheckerSound f1677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1677
  · intro a ha; simp [p1677] at ha; subst a; trivial
  · exact checked1677
theorem derived1677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1677 := by
  apply localUnsat_implies_entails f1677 [c1489, c1621, c1674, c1586, c389, c1641, c1651, c1287, c1587, c53, c378, c1579, c58, c108, c353, c62, c86, c42, c1675, c1676, c224, c22, c265, c220, c255, c209, c229, c281] c1677 unsat1677 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1586 := derived1586 a h
  have h4 : Entails.eval a c389 := h 388 (by decide)
  have h5 : Entails.eval a c1641 := derived1641 a h
  have h6 : Entails.eval a c1651 := derived1651 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c1587 := derived1587 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c1579 := derived1579 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c86 := h 85 (by decide)
  have h17 : Entails.eval a c42 := h 41 (by decide)
  have h18 : Entails.eval a c1675 := derived1675 a h
  have h19 : Entails.eval a c1676 := derived1676 a h
  have h20 : Entails.eval a c224 := h 223 (by decide)
  have h21 : Entails.eval a c22 := h 21 (by decide)
  have h22 : Entails.eval a c265 := h 264 (by decide)
  have h23 : Entails.eval a c220 := h 219 (by decide)
  have h24 : Entails.eval a c255 := h 254 (by decide)
  have h25 : Entails.eval a c209 := h 208 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  have h27 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1678 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1674, some c1641, some c1651, some c1586, some c1677, some c296, some c73, some c53, some c343, some c342, some c227, some c1040, some c1660, some c277, some c70, some c30, some c14, some c125, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1678 : lratChecker f1678 p1678 = .success := by decide +kernel
theorem unsat1678 : Unsatisfiable (PosFin 57) f1678 := by
  apply lratCheckerSound f1678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1678
  · intro a ha; simp [p1678] at ha; subst a; trivial
  · exact checked1678
theorem derived1678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1678 := by
  apply localUnsat_implies_entails f1678 [c1489, c1674, c1641, c1651, c1586, c1677, c296, c73, c53, c343, c342, c227, c1040, c1660, c277, c70, c30, c14, c125] c1678 unsat1678 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1674 := derived1674 a h
  have h2 : Entails.eval a c1641 := derived1641 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1586 := derived1586 a h
  have h5 : Entails.eval a c1677 := derived1677 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c1040 := derived1040 a h
  have h13 : Entails.eval a c1660 := derived1660 a h
  have h14 : Entails.eval a c277 := h 276 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1679 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c43, some c113, some c108, some c22, some c176, some c82, some c241, some c297, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1679 : lratChecker f1679 p1679 = .success := by decide +kernel
theorem unsat1679 : Unsatisfiable (PosFin 57) f1679 := by
  apply lratCheckerSound f1679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1679
  · intro a ha; simp [p1679] at ha; subst a; trivial
  · exact checked1679
theorem derived1679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1679 := by
  apply localUnsat_implies_entails f1679 [c1489, c43, c113, c108, c22, c176, c82, c241, c297] c1679 unsat1679 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1680 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c53, some c121, some c176, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1680 : lratChecker f1680 p1680 = .success := by decide +kernel
theorem unsat1680 : Unsatisfiable (PosFin 57) f1680 := by
  apply lratCheckerSound f1680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1680
  · intro a ha; simp [p1680] at ha; subst a; trivial
  · exact checked1680
theorem derived1680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1680 := by
  apply localUnsat_implies_entails f1680 [c1489, c53, c121, c176] c1680 unsat1680 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1681 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1674, some c1641, some c1651, some c1678, some c1210, some c1215, some c1221, some c1173, some c1663, some c1614, some c8, some c119, some c153, some c327, some c255, some c32, some c217, some c1679, some c1680, some c343, some c1537, some c1040, some c378, some c342, some c1023, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c1621, c1674, c1641, c1651, c1678, c1210, c1215, c1221, c1173, c1663, c1614, c8, c119, c153, c327, c255, c32, c217, c1679, c1680, c343, c1537, c1040, c378, c342, c1023] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1674 := derived1674 a h
  have h2 : Entails.eval a c1641 := derived1641 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1678 := derived1678 a h
  have h5 : Entails.eval a c1210 := derived1210 a h
  have h6 : Entails.eval a c1215 := derived1215 a h
  have h7 : Entails.eval a c1221 := derived1221 a h
  have h8 : Entails.eval a c1173 := derived1173 a h
  have h9 : Entails.eval a c1663 := derived1663 a h
  have h10 : Entails.eval a c1614 := derived1614 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c255 := h 254 (by decide)
  have h16 : Entails.eval a c32 := h 31 (by decide)
  have h17 : Entails.eval a c217 := h 216 (by decide)
  have h18 : Entails.eval a c1679 := derived1679 a h
  have h19 : Entails.eval a c1680 := derived1680 a h
  have h20 : Entails.eval a c343 := h 342 (by decide)
  have h21 : Entails.eval a c1537 := derived1537 a h
  have h22 : Entails.eval a c1040 := derived1040 a h
  have h23 : Entails.eval a c378 := h 377 (by decide)
  have h24 : Entails.eval a c342 := h 341 (by decide)
  have h25 : Entails.eval a c1023 := derived1023 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1674, some c1641, some c1681, some c59, some c52, some c92, some c575, some c378, some c343, some c53, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1621, c1489, c1674, c1641, c1681, c59, c52, c92, c575, c378, c343, c53] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1641 := derived1641 a h
  have h4 : Entails.eval a c1681 := derived1681 a h
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨50, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c43, some c42, some c324, some c327, some c312, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c1489, c43, c42, c324, c327, c312] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1684 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1651, some c1682, some c110, some c1214, some c1210, some c109, some c1674, some c986, some c112, some c388, some c1390, some c1683, some c296, some c280, some c53, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1489, c1651, c1682, c110, c1214, c1210, c109, c1674, c986, c112, c388, c1390, c1683, c296, c280, c53] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1682 := derived1682 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1214 := derived1214 a h
  have h5 : Entails.eval a c1210 := derived1210 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c986 := derived986 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c1390 := derived1390 a h
  have h12 : Entails.eval a c1683 := derived1683 a h
  have h13 : Entails.eval a c296 := h 295 (by decide)
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1210, some c1674, some c1651, some c1195, some c326, some c374, some c383, some c304, some c370, some c312, some c388, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c1210, c1674, c1651, c1195, c326, c374, c383, c304, c370, c312, c388] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c1210 := derived1210 a h
  have h1 : Entails.eval a c1674 := derived1674 a h
  have h2 : Entails.eval a c1651 := derived1651 a h
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c312 := h 311 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c318, some c304, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c374, c318, c304] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1682, some c109, some c1684, some c88, some c48, some c59, some c110, some c1674, some c1641, some c1651, some c343, some c53, some c63, some c378, some c1685, some c1686, some c389, some c353, some c1676, some c226, some c334, some c23, some c254, some c360, some c229, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1621, c1489, c1682, c109, c1684, c88, c48, c59, c110, c1674, c1641, c1651, c343, c53, c63, c378, c1685, c1686, c389, c353, c1676, c226, c334, c23, c254, c360, c229] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1682 := derived1682 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1684 := derived1684 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1674 := derived1674 a h
  have h10 : Entails.eval a c1641 := derived1641 a h
  have h11 : Entails.eval a c1651 := derived1651 a h
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c378 := h 377 (by decide)
  have h16 : Entails.eval a c1685 := derived1685 a h
  have h17 : Entails.eval a c1686 := derived1686 a h
  have h18 : Entails.eval a c389 := h 388 (by decide)
  have h19 : Entails.eval a c353 := h 352 (by decide)
  have h20 : Entails.eval a c1676 := derived1676 a h
  have h21 : Entails.eval a c226 := h 225 (by decide)
  have h22 : Entails.eval a c334 := h 333 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  have h24 : Entails.eval a c254 := h 253 (by decide)
  have h25 : Entails.eval a c360 := h 359 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1682, some c110, some c1210, some c1687, some c1287, some c73, some c296, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c1489, c1682, c110, c1210, c1687, c1287, c73, c296] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1682 := derived1682 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1210 := derived1210 a h
  have h4 : Entails.eval a c1687 := derived1687 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1689 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1688, some c1509, some c1674, some c1641, some c1651, some c92, some c78, some c389, some c93, some c34, some c74, some c96, some c1537, some c300, some c112, some c61, some c1663, some c62, some c281, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c1489, c1688, c1509, c1674, c1641, c1651, c92, c78, c389, c93, c34, c74, c96, c1537, c300, c112, c61, c1663, c62, c281] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1688 := derived1688 a h
  have h2 : Entails.eval a c1509 := derived1509 a h
  have h3 : Entails.eval a c1674 := derived1674 a h
  have h4 : Entails.eval a c1641 := derived1641 a h
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c1537 := derived1537 a h
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c1663 := derived1663 a h
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨26, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1688, some c1509, some c1674, some c1651, some c326, some c300, some c74, some c389, some c388, some c374, some c318, some c314, some c370, some c302, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c1688, c1509, c1674, c1651, c326, c300, c74, c389, c388, c374, c318, c314, c370, c302] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c1688 := derived1688 a h
  have h1 : Entails.eval a c1509 := derived1509 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c374 := h 373 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1689, some c1688, some c1674, some c1641, some c1651, some c1287, some c41, some c1690, some c1210, some c1215, some c1221, some c1173, some c1663, some c15, some c119, some c327, some c160, some c255, some c43, some c211, some c983, some c1680, some c29, some c342, some c126, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c1489, c1621, c1689, c1688, c1674, c1641, c1651, c1287, c41, c1690, c1210, c1215, c1221, c1173, c1663, c15, c119, c327, c160, c255, c43, c211, c983, c1680, c29, c342, c126] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1689 := derived1689 a h
  have h3 : Entails.eval a c1688 := derived1688 a h
  have h4 : Entails.eval a c1674 := derived1674 a h
  have h5 : Entails.eval a c1641 := derived1641 a h
  have h6 : Entails.eval a c1651 := derived1651 a h
  have h7 : Entails.eval a c1287 := derived1287 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c1690 := derived1690 a h
  have h10 : Entails.eval a c1210 := derived1210 a h
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1221 := derived1221 a h
  have h13 : Entails.eval a c1173 := derived1173 a h
  have h14 : Entails.eval a c1663 := derived1663 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c255 := h 254 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c211 := h 210 (by decide)
  have h22 : Entails.eval a c983 := derived983 a h
  have h23 : Entails.eval a c1680 := derived1680 a h
  have h24 : Entails.eval a c29 := h 28 (by decide)
  have h25 : Entails.eval a c342 := h 341 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1689, some c1688, some c1509, some c1674, some c1641, some c1651, some c1691, some c1668, some c1210, some c1215, some c1221, some c1173, some c1663, some c15, some c119, some c327, some c160, some c32, some c983, some c217, some c389, some c265, some c93, some c126, some c255, some c342, some c1680, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1621, c1489, c1689, c1688, c1509, c1674, c1641, c1651, c1691, c1668, c1210, c1215, c1221, c1173, c1663, c15, c119, c327, c160, c32, c983, c217, c389, c265, c93, c126, c255, c342, c1680] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1689 := derived1689 a h
  have h3 : Entails.eval a c1688 := derived1688 a h
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c1674 := derived1674 a h
  have h6 : Entails.eval a c1641 := derived1641 a h
  have h7 : Entails.eval a c1651 := derived1651 a h
  have h8 : Entails.eval a c1691 := derived1691 a h
  have h9 : Entails.eval a c1668 := derived1668 a h
  have h10 : Entails.eval a c1210 := derived1210 a h
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1221 := derived1221 a h
  have h13 : Entails.eval a c1173 := derived1173 a h
  have h14 : Entails.eval a c1663 := derived1663 a h
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c983 := derived983 a h
  have h21 : Entails.eval a c217 := h 216 (by decide)
  have h22 : Entails.eval a c389 := h 388 (by decide)
  have h23 : Entails.eval a c265 := h 264 (by decide)
  have h24 : Entails.eval a c93 := h 92 (by decide)
  have h25 : Entails.eval a c126 := h 125 (by decide)
  have h26 : Entails.eval a c255 := h 254 (by decide)
  have h27 : Entails.eval a c342 := h 341 (by decide)
  have h28 : Entails.eval a c1680 := derived1680 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1692

end CochromaticTwenty.Certificates.B16_6_2
