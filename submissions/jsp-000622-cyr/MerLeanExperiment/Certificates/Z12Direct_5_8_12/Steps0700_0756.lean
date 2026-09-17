import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0600_0699

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1617 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1617 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c28, some c7, some c1616, some c1513, some c417, some c521, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1617 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1617 : lratChecker f1617 p1617 = .success := by decide +kernel
theorem unsat1617 : Unsatisfiable (PosFin 31) f1617 := by
  apply lratCheckerSound f1617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1617
  · intro a ha; simp [p1617] at ha; subst a; trivial
  · exact checked1617
theorem derived1617 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1617 := by
  apply localUnsat_implies_entails f1617 [c1441, c1612, c28, c7, c1616, c1513, c417, c521] c1617 unsat1617 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1616 := derived1616 a h
  have h5 : Entails.eval a c1513 := derived1513 a h
  have h6 : Entails.eval a c417 := h 416 (by decide)
  have h7 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1618 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1618 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c1615, some c90, some c679, some c81, some c1233, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1618 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1618 : lratChecker f1618 p1618 = .success := by decide +kernel
theorem unsat1618 : Unsatisfiable (PosFin 31) f1618 := by
  apply lratCheckerSound f1618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1618
  · intro a ha; simp [p1618] at ha; subst a; trivial
  · exact checked1618
theorem derived1618 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1618 := by
  apply localUnsat_implies_entails f1618 [c1441, c1612, c1615, c90, c679, c81, c1233] c1618 unsat1618 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1615 := derived1615 a h
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c679 := h 678 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c1233 := derived1233 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1619 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c392, some c375, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1619 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 31) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c392, c375] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1620 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1617, some c1615, some c1618, some c1513, some c1298, some c262, some c560, some c77, some c1619, some c263, some c1297, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1620 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 31) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c1612, c1617, c1615, c1618, c1513, c1298, c262, c560, c77, c1619, c263, c1297] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1617 := derived1617 a h
  have h2 : Entails.eval a c1615 := derived1615 a h
  have h3 : Entails.eval a c1618 := derived1618 a h
  have h4 : Entails.eval a c1513 := derived1513 a h
  have h5 : Entails.eval a c1298 := derived1298 a h
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c560 := h 559 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c1619 := derived1619 a h
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c1297 := derived1297 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c892, some c1272, some c29, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p1621 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 31) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c1583, c1612, c892, c1272, c29] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c892 := h 891 (by decide)
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1583, some c1441, some c1615, some c1617, some c1620, some c1425, some c252, some c1234, some c81, some c1266, some c1621, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1622 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 31) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1612, c1583, c1441, c1615, c1617, c1620, c1425, c252, c1234, c81, c1266, c1621] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1615 := derived1615 a h
  have h4 : Entails.eval a c1617 := derived1617 a h
  have h5 : Entails.eval a c1620 := derived1620 a h
  have h6 : Entails.eval a c1425 := derived1425 a h
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c1234 := derived1234 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c1266 := derived1266 a h
  have h11 : Entails.eval a c1621 := derived1621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1622, some c1534, some c1618, some c1513, some c28, some c264, some c1298, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1623 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 31) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c1612, c1622, c1534, c1618, c1513, c28, c264, c1298] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1622 := derived1622 a h
  have h2 : Entails.eval a c1534 := derived1534 a h
  have h3 : Entails.eval a c1618 := derived1618 a h
  have h4 : Entails.eval a c1513 := derived1513 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c1298 := derived1298 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c1585, some c1298, some c81, some c679, some c1233, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1624 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 31) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1441, c1612, c1585, c1298, c81, c679, c1233] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1585 := derived1585 a h
  have h3 : Entails.eval a c1298 := derived1298 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c679 := h 678 (by decide)
  have h6 : Entails.eval a c1233 := derived1233 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1441, some c1583, some c1624, some c28, some c1513, some c1291, some c594, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1625 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 31) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1612, c1441, c1583, c1624, c28, c1513, c1291, c594] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1583 := derived1583 a h
  have h3 : Entails.eval a c1624 := derived1624 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1513 := derived1513 a h
  have h6 : Entails.eval a c1291 := derived1291 a h
  have h7 : Entails.eval a c594 := h 593 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c1612, some c1625, some c1425, some c28, some c297, some c241, some c14, some c335, some c1048, some c1242, some c243, some c245, some c1219, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1626 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 31) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1583, c1441, c1612, c1625, c1425, c28, c297, c241, c14, c335, c1048, c1242, c243, c245, c1219] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1625 := derived1625 a h
  have h4 : Entails.eval a c1425 := derived1425 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c335 := h 334 (by decide)
  have h10 : Entails.eval a c1048 := derived1048 a h
  have h11 : Entails.eval a c1242 := derived1242 a h
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  have h14 : Entails.eval a c1219 := derived1219 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1583, some c1612, some c1625, some c1425, some c1626, some c1585, some c1234, some c81, some c1621, some c1266, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1627 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 31) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1441, c1583, c1612, c1625, c1425, c1626, c1585, c1234, c81, c1621, c1266] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1625 := derived1625 a h
  have h4 : Entails.eval a c1425 := derived1425 a h
  have h5 : Entails.eval a c1626 := derived1626 a h
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c1234 := derived1234 a h
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c1621 := derived1621 a h
  have h10 : Entails.eval a c1266 := derived1266 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨14, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c343, some c284, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1628 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 31) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1583, c343, c284] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c1441, some c1425, some c1627, some c1623, some c1585, some c1234, some c1628, some c256, some c1204, some c18, some c1297, some c1278, some c149, some c412, some c289, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1629 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 31) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c1583, c1612, c1441, c1425, c1627, c1623, c1585, c1234, c1628, c256, c1204, c18, c1297, c1278, c149, c412, c289] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1425 := derived1425 a h
  have h4 : Entails.eval a c1627 := derived1627 a h
  have h5 : Entails.eval a c1623 := derived1623 a h
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c1234 := derived1234 a h
  have h8 : Entails.eval a c1628 := derived1628 a h
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c1204 := derived1204 a h
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1297 := derived1297 a h
  have h13 : Entails.eval a c1278 := derived1278 a h
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c412 := h 411 (by decide)
  have h16 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c1441, some c1425, some c1629, some c241, some c28, some c1627, some c1623, some c79, some c134, some c923, some c1206, some c21, some c491, some c480, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1630 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 31) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c1583, c1612, c1441, c1425, c1629, c241, c28, c1627, c1623, c79, c134, c923, c1206, c21, c491, c480] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1425 := derived1425 a h
  have h4 : Entails.eval a c1629 := derived1629 a h
  have h5 : Entails.eval a c241 := h 240 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c1627 := derived1627 a h
  have h8 : Entails.eval a c1623 := derived1623 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c923 := derived923 a h
  have h12 : Entails.eval a c1206 := derived1206 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c491 := h 490 (by decide)
  have h15 : Entails.eval a c480 := h 479 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1583, some c1441, some c1630, some c1629, some c28, some c1623, some c1313, some c307, some c82, some c491, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1631 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 31) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c1612, c1583, c1441, c1630, c1629, c28, c1623, c1313, c307, c82, c491] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1630 := derived1630 a h
  have h4 : Entails.eval a c1629 := derived1629 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1623 := derived1623 a h
  have h7 : Entails.eval a c1313 := derived1313 a h
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c491 := h 490 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1627, some c1623, some c1631, some c284, some c256, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1632 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 31) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c1583, c1627, c1623, c1631, c284, c256] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1627 := derived1627 a h
  have h2 : Entails.eval a c1623 := derived1623 a h
  have h3 : Entails.eval a c1631 := derived1631 a h
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c1612, some c1627, some c284, some c134, some c1007, some c1269, some c1228, some c541, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1633 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 31) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c1583, c1441, c1612, c1627, c284, c134, c1007, c1269, c1228, c541] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1627 := derived1627 a h
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c1007 := derived1007 a h
  have h7 : Entails.eval a c1269 := derived1269 a h
  have h8 : Entails.eval a c1228 := derived1228 a h
  have h9 : Entails.eval a c541 := h 540 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1633, some c1632, some c1204, some c28, some c1513, some c1313, some c195, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1634 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 31) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c1612, c1633, c1632, c1204, c28, c1513, c1313, c195] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1633 := derived1633 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1513 := derived1513 a h
  have h6 : Entails.eval a c1313 := derived1313 a h
  have h7 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c1633, some c79, some c1206, some c1632, some c1623, some c28, some c491, some c7, some c523, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1635 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 31) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1441, c1612, c1633, c79, c1206, c1632, c1623, c28, c491, c7, c523] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1633 := derived1633 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c1206 := derived1206 a h
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c1623 := derived1623 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c491 := h 490 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c523 := h 522 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1636 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1633, some c1627, some c1623, some c1634, some c79, some c1206, some c1635, some c1585, some c18, some c1278, some c149, some c159, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1636 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 31) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c1441, c1633, c1627, c1623, c1634, c79, c1206, c1635, c1585, c18, c1278, c149, c159] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1633 := derived1633 a h
  have h2 : Entails.eval a c1627 := derived1627 a h
  have h3 : Entails.eval a c1623 := derived1623 a h
  have h4 : Entails.eval a c1634 := derived1634 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c1206 := derived1206 a h
  have h7 : Entails.eval a c1635 := derived1635 a h
  have h8 : Entails.eval a c1585 := derived1585 a h
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1278 := derived1278 a h
  have h11 : Entails.eval a c149 := h 148 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1583, some c1623, some c1632, some c1633, some c1636, some c343, some c232, some c1585, some c28, some c491, some c1513, some c13, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1637 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 31) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c1612, c1583, c1623, c1632, c1633, c1636, c343, c232, c1585, c28, c491, c1513, c13] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1623 := derived1623 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c1633 := derived1633 a h
  have h5 : Entails.eval a c1636 := derived1636 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c1585 := derived1585 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c491 := h 490 (by decide)
  have h11 : Entails.eval a c1513 := derived1513 a h
  have h12 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c343, some c232, some c1206, some c285, some c286, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1638 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 31) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c1583, c343, c232, c1206, c285, c286] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c1206 := derived1206 a h
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1637, some c1583, some c370, some c1253, some c1249, some c1214, some c1245, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1639 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 31) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1441, c1637, c1583, c370, c1253, c1249, c1214, c1245] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1637 := derived1637 a h
  have h2 : Entails.eval a c1583 := derived1583 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c1249 := derived1249 a h
  have h6 : Entails.eval a c1214 := derived1214 a h
  have h7 : Entails.eval a c1245 := derived1245 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c343, some c232, some c1585, some c1206, some c1639, some c29, some c286, some c1638, some c1225, some c45, some c816, some c1386, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1640 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 31) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c1583, c343, c232, c1585, c1206, c1639, c29, c286, c1638, c1225, c45, c816, c1386] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c1585 := derived1585 a h
  have h4 : Entails.eval a c1206 := derived1206 a h
  have h5 : Entails.eval a c1639 := derived1639 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c286 := h 285 (by decide)
  have h8 : Entails.eval a c1638 := derived1638 a h
  have h9 : Entails.eval a c1225 := derived1225 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c816 := h 815 (by decide)
  have h12 : Entails.eval a c1386 := derived1386 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c14, some c3, some c1497, some c1315, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1641 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 31) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1612, c14, c3, c1497, c1315] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1497 := derived1497 a h
  have h4 : Entails.eval a c1315 := derived1315 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1637, some c1583, some c1441, some c343, some c232, some c1206, some c1585, some c29, some c1641, some c1640, some c140, some c1595, some c252, some c90, some c644, some c1225, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1642 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 31) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c1637, c1583, c1441, c343, c232, c1206, c1585, c29, c1641, c1640, c140, c1595, c252, c90, c644, c1225] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c1637 := derived1637 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c1206 := derived1206 a h
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c1641 := derived1641 a h
  have h9 : Entails.eval a c1640 := derived1640 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c1595 := derived1595 a h
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c644 := h 643 (by decide)
  have h15 : Entails.eval a c1225 := derived1225 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c1612, some c1642, some c343, some c232, some c1206, some c1585, some c140, some c433, some c90, some c659, some c706, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1643 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 31) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c1583, c1441, c1612, c1642, c343, c232, c1206, c1585, c140, c433, c90, c659, c706] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1642 := derived1642 a h
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c1206 := derived1206 a h
  have h7 : Entails.eval a c1585 := derived1585 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c433 := h 432 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c659 := h 658 (by decide)
  have h12 : Entails.eval a c706 := h 705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c659, some c610, some c614, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1644 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 31) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c1612, c659, c610, c614] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c659 := h 658 (by decide)
  have h2 : Entails.eval a c610 := h 609 (by decide)
  have h3 : Entails.eval a c614 := h 613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1441, some c1612, some c1643, some c343, some c1585, some c232, some c107, some c250, some c840, some c1314, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1645 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 31) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c1583, c1441, c1612, c1643, c343, c1585, c232, c107, c250, c840, c1314] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1643 := derived1643 a h
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c1585 := derived1585 a h
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c840 := h 839 (by decide)
  have h10 : Entails.eval a c1314 := derived1314 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c343, some c1585, some c232, some c29, some c1643, some c1645, some c1644, some c610, some c1120, some c840, some c793, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1646 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 31) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c1583, c1612, c343, c1585, c232, c29, c1643, c1645, c1644, c610, c1120, c840, c793] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c1585 := derived1585 a h
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1643 := derived1643 a h
  have h7 : Entails.eval a c1645 := derived1645 a h
  have h8 : Entails.eval a c1644 := derived1644 a h
  have h9 : Entails.eval a c610 := h 609 (by decide)
  have h10 : Entails.eval a c1120 := derived1120 a h
  have h11 : Entails.eval a c840 := h 839 (by decide)
  have h12 : Entails.eval a c793 := h 792 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1612, some c1583, some c343, some c29, some c232, some c1585, some c1206, some c1642, some c1646, some c14, some c594, some c215, some c1237, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1647 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 31) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1441, c1612, c1583, c343, c29, c232, c1585, c1206, c1642, c1646, c14, c594, c215, c1237] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1583 := derived1583 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c1585 := derived1585 a h
  have h7 : Entails.eval a c1206 := derived1206 a h
  have h8 : Entails.eval a c1642 := derived1642 a h
  have h9 : Entails.eval a c1646 := derived1646 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c594 := h 593 (by decide)
  have h12 : Entails.eval a c215 := h 214 (by decide)
  have h13 : Entails.eval a c1237 := derived1237 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1637, some c1206, some c1647, some c916, some c1459, some c1497, some c254, some c706, some c873, some c519, some c884, some c372, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1648 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 31) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1612, c1637, c1206, c1647, c916, c1459, c1497, c254, c706, c873, c519, c884, c372] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1637 := derived1637 a h
  have h2 : Entails.eval a c1206 := derived1206 a h
  have h3 : Entails.eval a c1647 := derived1647 a h
  have h4 : Entails.eval a c916 := h 915 (by decide)
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c1497 := derived1497 a h
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c706 := h 705 (by decide)
  have h9 : Entails.eval a c873 := h 872 (by decide)
  have h10 : Entails.eval a c519 := h 518 (by decide)
  have h11 : Entails.eval a c884 := h 883 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1612, some c1637, some c916, some c1206, some c1459, some c1648, some c1585, some c1203, some c1297, some c1370, some c337, some c140, some c1323, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1649 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 31) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c1583, c1612, c1637, c916, c1206, c1459, c1648, c1585, c1203, c1297, c1370, c337, c140, c1323] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1612 := derived1612 a h
  have h2 : Entails.eval a c1637 := derived1637 a h
  have h3 : Entails.eval a c916 := h 915 (by decide)
  have h4 : Entails.eval a c1206 := derived1206 a h
  have h5 : Entails.eval a c1459 := derived1459 a h
  have h6 : Entails.eval a c1648 := derived1648 a h
  have h7 : Entails.eval a c1585 := derived1585 a h
  have h8 : Entails.eval a c1203 := derived1203 a h
  have h9 : Entails.eval a c1297 := derived1297 a h
  have h10 : Entails.eval a c1370 := derived1370 a h
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c1323 := derived1323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1441, some c591, some c1459, some c1497, some c254, some c704, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1650 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 31) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c1612, c1441, c591, c1459, c1497, c254, c704] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c591 := h 590 (by decide)
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c1497 := derived1497 a h
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c704 := h 703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1637, some c1441, some c1612, some c1649, some c79, some c1204, some c1650, some c824, some c282, some c231, some c408, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1651 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 31) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c1637, c1441, c1612, c1649, c79, c1204, c1650, c824, c282, c231, c408] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c1637 := derived1637 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1649 := derived1649 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1204 := derived1204 a h
  have h6 : Entails.eval a c1650 := derived1650 a h
  have h7 : Entails.eval a c824 := h 823 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c408 := h 407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1647, some c1651, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1652 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 31) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c1647, c1651] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c1647 := derived1647 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1653 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1583, some c1652, some c1612, some c79, some c53, some c161, some c313, some c1228, some c55, some c1513, some c692, some c1233, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1653 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 31) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c1441, c1583, c1652, c1612, c79, c53, c161, c313, c1228, c55, c1513, c692, c1233] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1652 := derived1652 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c1228 := derived1228 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c1513 := derived1513 a h
  have h11 : Entails.eval a c692 := h 691 (by decide)
  have h12 : Entails.eval a c1233 := derived1233 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1654 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1652, some c1441, some c1612, some c79, some c1653, some c1207, some c1650, some c1204, some c284, some c189, some c1319, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1654 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 31) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1583, c1652, c1441, c1612, c79, c1653, c1207, c1650, c1204, c284, c189, c1319] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c1653 := derived1653 a h
  have h6 : Entails.eval a c1207 := derived1207 a h
  have h7 : Entails.eval a c1650 := derived1650 a h
  have h8 : Entails.eval a c1204 := derived1204 a h
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c1319 := derived1319 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1652, some c1654, some c1612, some c1583, some c1228, some c735, some c541, some c29, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1655 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 31) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1652, c1654, c1612, c1583, c1228, c735, c541, c29] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1652 := derived1652 a h
  have h1 : Entails.eval a c1654 := derived1654 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1583 := derived1583 a h
  have h4 : Entails.eval a c1228 := derived1228 a h
  have h5 : Entails.eval a c735 := h 734 (by decide)
  have h6 : Entails.eval a c541 := h 540 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c254, some c309, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1656 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 31) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1612, c254, c309] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c254 := h 253 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1652, some c1655, some c1621, some c1007, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1657 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 31) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1441, c1652, c1655, c1621, c1007] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1655 := derived1655 a h
  have h3 : Entails.eval a c1621 := derived1621 a h
  have h4 : Entails.eval a c1007 := derived1007 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1441, some c1652, some c1459, some c1656, some c1657, some c1495, some c517, some c1497, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1658 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 31) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c1612, c1441, c1652, c1459, c1656, c1657, c1495, c517, c1497] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1441 := derived1441 a h
  have h2 : Entails.eval a c1652 := derived1652 a h
  have h3 : Entails.eval a c1459 := derived1459 a h
  have h4 : Entails.eval a c1656 := derived1656 a h
  have h5 : Entails.eval a c1657 := derived1657 a h
  have h6 : Entails.eval a c1495 := derived1495 a h
  have h7 : Entails.eval a c517 := h 516 (by decide)
  have h8 : Entails.eval a c1497 := derived1497 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1652, some c1441, some c1612, some c1654, some c1658, some c1425, some c134, some c1048, some c183, some c737, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1659 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 31) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1583, c1652, c1441, c1612, c1654, c1658, c1425, c134, c1048, c183, c737] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c1654 := derived1654 a h
  have h5 : Entails.eval a c1658 := derived1658 a h
  have h6 : Entails.eval a c1425 := derived1425 a h
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c1048 := derived1048 a h
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c737 := h 736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1583, some c1654, some c1652, some c1612, some c1658, some c1425, some c1659, some c1308, some c1203, some c737, some c1641, some c254, some c1228, some c896, some c261, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p1660 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 31) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c1583, c1654, c1652, c1612, c1658, c1425, c1659, c1308, c1203, c737, c1641, c254, c1228, c896, c261] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c1583 := derived1583 a h
  have h1 : Entails.eval a c1654 := derived1654 a h
  have h2 : Entails.eval a c1652 := derived1652 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c1658 := derived1658 a h
  have h5 : Entails.eval a c1425 := derived1425 a h
  have h6 : Entails.eval a c1659 := derived1659 a h
  have h7 : Entails.eval a c1308 := derived1308 a h
  have h8 : Entails.eval a c1203 := derived1203 a h
  have h9 : Entails.eval a c737 := h 736 (by decide)
  have h10 : Entails.eval a c1641 := derived1641 a h
  have h11 : Entails.eval a c254 := h 253 (by decide)
  have h12 : Entails.eval a c1228 := derived1228 a h
  have h13 : Entails.eval a c896 := h 895 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1660, some c1583, some c1612, some c1654, some c645, some c1305, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1661 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 31) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c1660, c1583, c1612, c1654, c645, c1305] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c1660 := derived1660 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1654 := derived1654 a h
  have h4 : Entails.eval a c645 := h 644 (by decide)
  have h5 : Entails.eval a c1305 := derived1305 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1612, some c1583, some c1425, some c1661, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1662 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 31) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c1612, c1583, c1425, c1661] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c1612 := derived1612 a h
  have h1 : Entails.eval a c1583 := derived1583 a h
  have h2 : Entails.eval a c1425 := derived1425 a h
  have h3 : Entails.eval a c1661 := derived1661 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1637, some c1660, some c1612, some c1441, some c1652, some c1662, some c1583, some c29, some c5, some c283, some c134, some c1007, some c1242, some c1655, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1663 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 31) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1637, c1660, c1612, c1441, c1652, c1662, c1583, c29, c5, c283, c134, c1007, c1242, c1655] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1637 := derived1637 a h
  have h1 : Entails.eval a c1660 := derived1660 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c1441 := derived1441 a h
  have h4 : Entails.eval a c1652 := derived1652 a h
  have h5 : Entails.eval a c1662 := derived1662 a h
  have h6 : Entails.eval a c1583 := derived1583 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c1007 := derived1007 a h
  have h12 : Entails.eval a c1242 := derived1242 a h
  have h13 : Entails.eval a c1655 := derived1655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1663, some c1654, some c1203, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1664 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 31) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1663, c1654, c1203] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1663 := derived1663 a h
  have h1 : Entails.eval a c1654 := derived1654 a h
  have h2 : Entails.eval a c1203 := derived1203 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1441, some c1652, some c1663, some c1612, some c1660, some c1637, some c1662, some c1654, some c1583, some c1207, some c161, some c313, some c1228, some c735, some c1262, some c1245, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1665 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 31) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c1441, c1652, c1663, c1612, c1660, c1637, c1662, c1654, c1583, c1207, c161, c313, c1228, c735, c1262, c1245] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c1441 := derived1441 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1663 := derived1663 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c1660 := derived1660 a h
  have h5 : Entails.eval a c1637 := derived1637 a h
  have h6 : Entails.eval a c1662 := derived1662 a h
  have h7 : Entails.eval a c1654 := derived1654 a h
  have h8 : Entails.eval a c1583 := derived1583 a h
  have h9 : Entails.eval a c1207 := derived1207 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c1228 := derived1228 a h
  have h13 : Entails.eval a c735 := h 734 (by decide)
  have h14 : Entails.eval a c1262 := derived1262 a h
  have h15 : Entails.eval a c1245 := derived1245 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1665, some c1652, some c1441, some c134, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1666 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 31) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1665, c1652, c1441, c134] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1441 := derived1441 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1667 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1665, some c1652, some c1598, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1667 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 31) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1665, c1652, c1598] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c1652 := derived1652 a h
  have h2 : Entails.eval a c1598 := derived1598 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1666, some c1660, some c1583, some c1612, some c1291, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1668 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 31) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1666, c1660, c1583, c1612, c1291] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1666 := derived1666 a h
  have h1 : Entails.eval a c1660 := derived1660 a h
  have h2 : Entails.eval a c1583 := derived1583 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c1291 := derived1291 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1666, some c1663, some c1612, some c14, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1669 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 31) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1666, c1663, c1612, c14] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1666 := derived1666 a h
  have h1 : Entails.eval a c1663 := derived1663 a h
  have h2 : Entails.eval a c1612 := derived1612 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1666, some c1662, some c1660, some c1663, some c1316, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1670 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 31) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c1666, c1662, c1660, c1663, c1316] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c1666 := derived1666 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c1660 := derived1660 a h
  have h3 : Entails.eval a c1663 := derived1663 a h
  have h4 : Entails.eval a c1316 := derived1316 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1663, some c1662, some c1660, some c1612, some c1666, some c1654, some c1637, some c1669, some c1668, some c622, some c739, some c283, some c720, some c555, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1671 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 31) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1663, c1662, c1660, c1612, c1666, c1654, c1637, c1669, c1668, c622, c739, c283, c720, c555] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1663 := derived1663 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c1660 := derived1660 a h
  have h3 : Entails.eval a c1612 := derived1612 a h
  have h4 : Entails.eval a c1666 := derived1666 a h
  have h5 : Entails.eval a c1654 := derived1654 a h
  have h6 : Entails.eval a c1637 := derived1637 a h
  have h7 : Entails.eval a c1669 := derived1669 a h
  have h8 : Entails.eval a c1668 := derived1668 a h
  have h9 : Entails.eval a c622 := h 621 (by decide)
  have h10 : Entails.eval a c739 := h 738 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c720 := h 719 (by decide)
  have h13 : Entails.eval a c555 := h 554 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1669, some c1665, some c1664, some c1667, some c1441, some c215, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p1672 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 31) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1669, c1665, c1664, c1667, c1441, c215] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1669 := derived1669 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1664 := derived1664 a h
  have h3 : Entails.eval a c1667 := derived1667 a h
  have h4 : Entails.eval a c1441 := derived1441 a h
  have h5 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1669, some c1670, some c1664, some c1652, some c1672, some c1671, some c328]
def p1673 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 31) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c1669, c1670, c1664, c1652, c1672, c1671, c328] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c1669 := derived1669 a h
  have h1 : Entails.eval a c1670 := derived1670 a h
  have h2 : Entails.eval a c1664 := derived1664 a h
  have h3 : Entails.eval a c1652 := derived1652 a h
  have h4 : Entails.eval a c1672 := derived1672 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1673

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
