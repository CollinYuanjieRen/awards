import MerLeanExperiment.Certificates.B16_6_2.Steps1200_1299

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1693 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1688, some c1692, some c45, some c1690, some c1210, some c1689, some c1215, some c15, some c1651, some c1674, some c85, some c180, some c1324, some c59, some c1509, some c1641, some c343, some c53, some c1680, some c176, some c255, some c119, some c252, some c208, some c254, some c1003, some c194, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1489, c1621, c1688, c1692, c45, c1690, c1210, c1689, c1215, c15, c1651, c1674, c85, c180, c1324, c59, c1509, c1641, c343, c53, c1680, c176, c255, c119, c252, c208, c254, c1003, c194] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1688 := derived1688 a h
  have h3 : Entails.eval a c1692 := derived1692 a h
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c1690 := derived1690 a h
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1689 := derived1689 a h
  have h8 : Entails.eval a c1215 := derived1215 a h
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c1651 := derived1651 a h
  have h11 : Entails.eval a c1674 := derived1674 a h
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c1324 := derived1324 a h
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c1509 := derived1509 a h
  have h17 : Entails.eval a c1641 := derived1641 a h
  have h18 : Entails.eval a c343 := h 342 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c1680 := derived1680 a h
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c255 := h 254 (by decide)
  have h23 : Entails.eval a c119 := h 118 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  have h25 : Entails.eval a c208 := h 207 (by decide)
  have h26 : Entails.eval a c254 := h 253 (by decide)
  have h27 : Entails.eval a c1003 := derived1003 a h
  have h28 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1694 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1674, some c1651, some c1688, some c1509, some c1692, some c45, some c1690, some c1221, some c1693, some c1287, some c73, some c93, some c293, some c389, some c374, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c1621, c1489, c1674, c1651, c1688, c1509, c1692, c45, c1690, c1221, c1693, c1287, c73, c93, c293, c389, c374] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1688 := derived1688 a h
  have h5 : Entails.eval a c1509 := derived1509 a h
  have h6 : Entails.eval a c1692 := derived1692 a h
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c1690 := derived1690 a h
  have h9 : Entails.eval a c1221 := derived1221 a h
  have h10 : Entails.eval a c1693 := derived1693 a h
  have h11 : Entails.eval a c1287 := derived1287 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c389 := h 388 (by decide)
  have h16 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1287, some c1694, some c1211, some c110, some c1651, some c1224, some c1674, some c78, some c58, some c1579, some c1675, some c108, some c46, some c86, some c1048, some c302, some c119, some c1660, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1621, c1287, c1694, c1211, c110, c1651, c1224, c1674, c78, c58, c1579, c1675, c108, c46, c86, c1048, c302, c119, c1660] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c1579 := derived1579 a h
  have h11 : Entails.eval a c1675 := derived1675 a h
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c1048 := derived1048 a h
  have h16 : Entails.eval a c302 := h 301 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c1660 := derived1660 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1651, some c1694, some c1224, some c1674, some c102, some c38, some c112, some c326, some c1523, some c42, some c98, some c313, some c312, some c302, some c1052, some c55, some c227, some c351, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1489, c1621, c1651, c1694, c1224, c1674, c102, c38, c112, c326, c1523, c42, c98, c313, c312, c302, c1052, c55, c227, c351] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1651 := derived1651 a h
  have h3 : Entails.eval a c1694 := derived1694 a h
  have h4 : Entails.eval a c1224 := derived1224 a h
  have h5 : Entails.eval a c1674 := derived1674 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c1523 := derived1523 a h
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c313 := h 312 (by decide)
  have h14 : Entails.eval a c312 := h 311 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c1052 := derived1052 a h
  have h17 : Entails.eval a c55 := h 54 (by decide)
  have h18 : Entails.eval a c227 := h 226 (by decide)
  have h19 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨27, by decide⟩, false), (⟨54, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1674, some c389, some c1694, some c313, some c369, some c1646, some c326, some c381, some c1052, some c248, some c220, some c265, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c1621, c1674, c389, c1694, c313, c369, c1646, c326, c381, c1052, c248, c220, c265] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1674 := derived1674 a h
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c1694 := derived1694 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c1646 := derived1646 a h
  have h7 : Entails.eval a c326 := h 325 (by decide)
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c1052 := derived1052 a h
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1694, some c1222, some c1052, some c55, some c227, some c351, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c1694, c1222, c1052, c55, c227, c351] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c1694 := derived1694 a h
  have h1 : Entails.eval a c1222 := derived1222 a h
  have h2 : Entails.eval a c1052 := derived1052 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c227 := h 226 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1694, some c1211, some c110, some c1651, some c1224, some c1674, some c1695, some c1696, some c389, some c1305, some c42, some c1697, some c1698, some c1048, some c302, some c119, some c1660, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1489, c1621, c1694, c1211, c110, c1651, c1224, c1674, c1695, c1696, c389, c1305, c42, c1697, c1698, c1048, c302, c119, c1660] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c1695 := derived1695 a h
  have h9 : Entails.eval a c1696 := derived1696 a h
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c1305 := derived1305 a h
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c1697 := derived1697 a h
  have h14 : Entails.eval a c1698 := derived1698 a h
  have h15 : Entails.eval a c1048 := derived1048 a h
  have h16 : Entails.eval a c302 := h 301 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c1660 := derived1660 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1287, some c1694, some c1211, some c110, some c1651, some c1224, some c1674, some c1699, some c79, some c59, some c52, some c92, some c343, some c326, some c1014, some c108, some c1523, some c42, some c62, some c312, some c351, some c302, some c1222, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c1621, c1489, c1287, c1694, c1211, c110, c1651, c1224, c1674, c1699, c79, c59, c52, c92, c343, c326, c1014, c108, c1523, c42, c62, c312, c351, c302, c1222] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1694 := derived1694 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1651 := derived1651 a h
  have h7 : Entails.eval a c1224 := derived1224 a h
  have h8 : Entails.eval a c1674 := derived1674 a h
  have h9 : Entails.eval a c1699 := derived1699 a h
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c1014 := derived1014 a h
  have h17 : Entails.eval a c108 := h 107 (by decide)
  have h18 : Entails.eval a c1523 := derived1523 a h
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c62 := h 61 (by decide)
  have h21 : Entails.eval a c312 := h 311 (by decide)
  have h22 : Entails.eval a c351 := h 350 (by decide)
  have h23 : Entails.eval a c302 := h 301 (by decide)
  have h24 : Entails.eval a c1222 := derived1222 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1651, some c1221, some c1694, some c1224, some c1173, some c119, some c147, some c1052, some c1663, some c302, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1621, c1651, c1221, c1694, c1224, c1173, c119, c147, c1052, c1663, c302] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1694 := derived1694 a h
  have h4 : Entails.eval a c1224 := derived1224 a h
  have h5 : Entails.eval a c1173 := derived1173 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c1052 := derived1052 a h
  have h9 : Entails.eval a c1663 := derived1663 a h
  have h10 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1694, some c1211, some c110, some c1651, some c1224, some c1674, some c1287, some c1700, some c1215, some c1221, some c8, some c1701, some c79, some c59, some c1299, some c1366, some c343, some c142, some c192, some c108, some c53, some c173, some c42, some c62, some c161, some c281, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c1621, c1489, c1694, c1211, c110, c1651, c1224, c1674, c1287, c1700, c1215, c1221, c8, c1701, c79, c59, c1299, c1366, c343, c142, c192, c108, c53, c173, c42, c62, c161, c281] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c1287 := derived1287 a h
  have h9 : Entails.eval a c1700 := derived1700 a h
  have h10 : Entails.eval a c1215 := derived1215 a h
  have h11 : Entails.eval a c1221 := derived1221 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c1701 := derived1701 a h
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c1299 := derived1299 a h
  have h17 : Entails.eval a c1366 := derived1366 a h
  have h18 : Entails.eval a c343 := h 342 (by decide)
  have h19 : Entails.eval a c142 := h 141 (by decide)
  have h20 : Entails.eval a c192 := h 191 (by decide)
  have h21 : Entails.eval a c108 := h 107 (by decide)
  have h22 : Entails.eval a c53 := h 52 (by decide)
  have h23 : Entails.eval a c173 := h 172 (by decide)
  have h24 : Entails.eval a c42 := h 41 (by decide)
  have h25 : Entails.eval a c62 := h 61 (by decide)
  have h26 : Entails.eval a c161 := h 160 (by decide)
  have h27 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1694, some c1211, some c110, some c1702, some c322, some c38, some c1340, some c1651, some c1224, some c1652, some c1697, some c293, some c58, some c73, some c53, some c342, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1489, c1694, c1211, c110, c1702, c322, c38, c1340, c1651, c1224, c1652, c1697, c293, c58, c73, c53, c342] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1702 := derived1702 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c1340 := derived1340 a h
  have h8 : Entails.eval a c1651 := derived1651 a h
  have h9 : Entails.eval a c1224 := derived1224 a h
  have h10 : Entails.eval a c1652 := derived1652 a h
  have h11 : Entails.eval a c1697 := derived1697 a h
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c73, some c53, some c1537, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c1489, c73, c53, c1537] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c1537 := derived1537 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1651, some c1694, some c1224, some c293, some c302, some c73, some c53, some c1052, some c343, some c227, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c1489, c1651, c1694, c1224, c293, c302, c73, c53, c1052, c343, c227] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1224 := derived1224 a h
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c1052 := derived1052 a h
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1702, some c1694, some c1211, some c110, some c1340, some c1651, some c1703, some c1705, some c37, some c112, some c1054, some c1698, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c1702, c1694, c1211, c110, c1340, c1651, c1703, c1705, c37, c112, c1054, c1698] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c1702 := derived1702 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1340 := derived1340 a h
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1703 := derived1703 a h
  have h7 : Entails.eval a c1705 := derived1705 a h
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c1054 := derived1054 a h
  have h11 : Entails.eval a c1698 := derived1698 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1702, some c1694, some c1211, some c110, some c1651, some c1224, some c1674, some c322, some c1340, some c38, some c1706, some c46, some c108, some c112, some c1549, some c37, some c63, some c293, some c277, some c73, some c70, some c342, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c1489, c1702, c1694, c1211, c110, c1651, c1224, c1674, c322, c1340, c38, c1706, c46, c108, c112, c1549, c37, c63, c293, c277, c73, c70, c342] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1702 := derived1702 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c1340 := derived1340 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c1706 := derived1706 a h
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c1549 := derived1549 a h
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c277 := h 276 (by decide)
  have h20 : Entails.eval a c73 := h 72 (by decide)
  have h21 : Entails.eval a c70 := h 69 (by decide)
  have h22 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1651, some c1694, some c1224, some c1702, some c1707, some c1221, some c1701, some c293, some c79, some c59, some c73, some c53, some c343, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c1489, c1651, c1694, c1224, c1702, c1707, c1221, c1701, c293, c79, c59, c73, c53, c343] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1651 := derived1651 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c1224 := derived1224 a h
  have h4 : Entails.eval a c1702 := derived1702 a h
  have h5 : Entails.eval a c1707 := derived1707 a h
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c1701 := derived1701 a h
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1708, some c41, some c326, some c1694, some c1674, some c1651, some c38, some c389, some c74, some c1305, some c42, some c297, some c86, some c1698, some c1697, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c1489, c1708, c41, c326, c1694, c1674, c1651, c38, c389, c74, c1305, c42, c297, c86, c1698, c1697] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c1694 := derived1694 a h
  have h5 : Entails.eval a c1674 := derived1674 a h
  have h6 : Entails.eval a c1651 := derived1651 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c1305 := derived1305 a h
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c1698 := derived1698 a h
  have h15 : Entails.eval a c1697 := derived1697 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c216, some c220, some c29, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c1621, c216, c220, c29] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1709, some c1708, some c41, some c326, some c1651, some c1694, some c1224, some c324, some c43, some c1710, some c1052, some c302, some c297, some c1316, some c74, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c1489, c1709, c1708, c41, c326, c1651, c1694, c1224, c324, c43, c1710, c1052, c302, c297, c1316, c74] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1709 := derived1709 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1694 := derived1694 a h
  have h7 : Entails.eval a c1224 := derived1224 a h
  have h8 : Entails.eval a c324 := h 323 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c1710 := derived1710 a h
  have h11 : Entails.eval a c1052 := derived1052 a h
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c1316 := derived1316 a h
  have h15 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1708, some c41, some c326, some c1694, some c1674, some c1651, some c1711, some c42, some c1305, some c389, some c388, some c314, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1489, c1708, c41, c326, c1694, c1674, c1651, c1711, c42, c1305, c389, c388, c314] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c1694 := derived1694 a h
  have h5 : Entails.eval a c1674 := derived1674 a h
  have h6 : Entails.eval a c1651 := derived1651 a h
  have h7 : Entails.eval a c1711 := derived1711 a h
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1305 := derived1305 a h
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1713 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1708, some c41, some c1287, some c1651, some c1694, some c1224, some c1211, some c326, some c1712, some c79, some c59, some c52, some c343, some c53, some c61, some c284, some c228, some c31, some c220, some c118, some c255, some c15, some c113, some c1218, some c173, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1713 : lratChecker f1713 p1713 = .success := by decide +kernel
theorem unsat1713 : Unsatisfiable (PosFin 57) f1713 := by
  apply lratCheckerSound f1713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1713
  · intro a ha; simp [p1713] at ha; subst a; trivial
  · exact checked1713
theorem derived1713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1713 := by
  apply localUnsat_implies_entails f1713 [c1489, c1621, c1708, c41, c1287, c1651, c1694, c1224, c1211, c326, c1712, c79, c59, c52, c343, c53, c61, c284, c228, c31, c220, c118, c255, c15, c113, c1218, c173] c1713 unsat1713 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c1694 := derived1694 a h
  have h7 : Entails.eval a c1224 := derived1224 a h
  have h8 : Entails.eval a c1211 := derived1211 a h
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c1712 := derived1712 a h
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c220 := h 219 (by decide)
  have h21 : Entails.eval a c118 := h 117 (by decide)
  have h22 : Entails.eval a c255 := h 254 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c113 := h 112 (by decide)
  have h25 : Entails.eval a c1218 := derived1218 a h
  have h26 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1714 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1708, some c1287, some c1713, some c1701, some c59, some c79, some c343, some c61, some c85, some c1651, some c1221, some c1215, some c41, some c1694, some c1674, some c297, some c281, some c1222, some c55, some c388, some c1303, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c1489, c1708, c1287, c1713, c1701, c59, c79, c343, c61, c85, c1651, c1221, c1215, c41, c1694, c1674, c297, c281, c1222, c55, c388, c1303] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1287 := derived1287 a h
  have h3 : Entails.eval a c1713 := derived1713 a h
  have h4 : Entails.eval a c1701 := derived1701 a h
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c343 := h 342 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c1651 := derived1651 a h
  have h11 : Entails.eval a c1221 := derived1221 a h
  have h12 : Entails.eval a c1215 := derived1215 a h
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c1694 := derived1694 a h
  have h15 : Entails.eval a c1674 := derived1674 a h
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c281 := h 280 (by decide)
  have h18 : Entails.eval a c1222 := derived1222 a h
  have h19 : Entails.eval a c55 := h 54 (by decide)
  have h20 : Entails.eval a c388 := h 387 (by decide)
  have h21 : Entails.eval a c1303 := derived1303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1694, some c1674, some c1651, some c1713, some c1215, some c1221, some c1701, some c1714, some c1219, some c42, some c388, some c1303, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c1489, c1694, c1674, c1651, c1713, c1215, c1221, c1701, c1714, c1219, c42, c388, c1303] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1674 := derived1674 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1713 := derived1713 a h
  have h5 : Entails.eval a c1215 := derived1215 a h
  have h6 : Entails.eval a c1221 := derived1221 a h
  have h7 : Entails.eval a c1701 := derived1701 a h
  have h8 : Entails.eval a c1714 := derived1714 a h
  have h9 : Entails.eval a c1219 := derived1219 a h
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c1303 := derived1303 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1715, some c1701, some c322, some c1708, some c1674, some c1651, some c38, some c389, some c34, some c74, some c96, some c112, some c46, some c297, some c1698, some c86, some c1697, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c1715, c1701, c322, c1708, c1674, c1651, c38, c389, c34, c74, c96, c112, c46, c297, c1698, c86, c1697] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c1715 := derived1715 a h
  have h1 : Entails.eval a c1701 := derived1701 a h
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c1708 := derived1708 a h
  have h4 : Entails.eval a c1674 := derived1674 a h
  have h5 : Entails.eval a c1651 := derived1651 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c1698 := derived1698 a h
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c1697 := derived1697 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1715, some c1701, some c322, some c1651, some c1694, some c1224, some c1211, some c1674, some c37, some c1652, some c1660, some c318, some c112, some c1698, some c119, some c383, some c32, some c30, some c249, some c1047, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c1621, c1715, c1701, c322, c1651, c1694, c1224, c1211, c1674, c37, c1652, c1660, c318, c112, c1698, c119, c383, c32, c30, c249, c1047] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1715 := derived1715 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c1651 := derived1651 a h
  have h5 : Entails.eval a c1694 := derived1694 a h
  have h6 : Entails.eval a c1224 := derived1224 a h
  have h7 : Entails.eval a c1211 := derived1211 a h
  have h8 : Entails.eval a c1674 := derived1674 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c1652 := derived1652 a h
  have h11 : Entails.eval a c1660 := derived1660 a h
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c1698 := derived1698 a h
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c383 := h 382 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c30 := h 29 (by decide)
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c1047 := derived1047 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1715, some c1651, some c1694, some c1224, some c1211, some c1701, some c322, some c1716, some c1717, some c293, some c53, some c280, some c228, some c32, some c31, some c220, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c1489, c1621, c1715, c1651, c1694, c1224, c1211, c1701, c322, c1716, c1717, c293, c53, c280, c228, c32, c31, c220] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1715 := derived1715 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1694 := derived1694 a h
  have h5 : Entails.eval a c1224 := derived1224 a h
  have h6 : Entails.eval a c1211 := derived1211 a h
  have h7 : Entails.eval a c1701 := derived1701 a h
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c1716 := derived1716 a h
  have h10 : Entails.eval a c1717 := derived1717 a h
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1719 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1718, some c59, some c79, some c73, some c53, some c343, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1719 : lratChecker f1719 p1719 = .success := by decide +kernel
theorem unsat1719 : Unsatisfiable (PosFin 57) f1719 := by
  apply lratCheckerSound f1719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1719
  · intro a ha; simp [p1719] at ha; subst a; trivial
  · exact checked1719
theorem derived1719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1719 := by
  apply localUnsat_implies_entails f1719 [c1489, c1718, c59, c79, c73, c53, c343] c1719 unsat1719 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1718 := derived1718 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1720 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1719, some c1651, some c1694, some c1224, some c1715, some c293, some c145, some c173, some c1718, some c59, some c79, some c1708, some c1674, some c318, some c389, some c93, some c343, some c121, some c255, some c254, some c220, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1720 : lratChecker f1720 p1720 = .success := by decide +kernel
theorem unsat1720 : Unsatisfiable (PosFin 57) f1720 := by
  apply lratCheckerSound f1720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1720
  · intro a ha; simp [p1720] at ha; subst a; trivial
  · exact checked1720
theorem derived1720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1720 := by
  apply localUnsat_implies_entails f1720 [c1489, c1621, c1719, c1651, c1694, c1224, c1715, c293, c145, c173, c1718, c59, c79, c1708, c1674, c318, c389, c93, c343, c121, c255, c254, c220] c1720 unsat1720 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1719 := derived1719 a h
  have h3 : Entails.eval a c1651 := derived1651 a h
  have h4 : Entails.eval a c1694 := derived1694 a h
  have h5 : Entails.eval a c1224 := derived1224 a h
  have h6 : Entails.eval a c1715 := derived1715 a h
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c173 := h 172 (by decide)
  have h10 : Entails.eval a c1718 := derived1718 a h
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c1708 := derived1708 a h
  have h14 : Entails.eval a c1674 := derived1674 a h
  have h15 : Entails.eval a c318 := h 317 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c343 := h 342 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c255 := h 254 (by decide)
  have h21 : Entails.eval a c254 := h 253 (by decide)
  have h22 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1721 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1651, some c1694, some c1224, some c1715, some c1719, some c293, some c1720, some c1221, some c322, some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1721 : lratChecker f1721 p1721 = .success := by decide +kernel
theorem unsat1721 : Unsatisfiable (PosFin 57) f1721 := by
  apply lratCheckerSound f1721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1721
  · intro a ha; simp [p1721] at ha; subst a; trivial
  · exact checked1721
theorem derived1721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1721 := by
  apply localUnsat_implies_entails f1721 [c1651, c1694, c1224, c1715, c1719, c293, c1720, c1221, c322] c1721 unsat1721 (by rfl) a
  have h0 : Entails.eval a c1651 := derived1651 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1224 := derived1224 a h
  have h3 : Entails.eval a c1715 := derived1715 a h
  have h4 : Entails.eval a c1719 := derived1719 a h
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c1720 := derived1720 a h
  have h7 : Entails.eval a c1221 := derived1221 a h
  have h8 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1722 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1721, some c379, some c53, some c1287, some c385, some c341, some c147, some c188, some c839, some c1118, some c201, some c171, some c1117, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1722 : lratChecker f1722 p1722 = .success := by decide +kernel
theorem unsat1722 : Unsatisfiable (PosFin 57) f1722 := by
  apply lratCheckerSound f1722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1722
  · intro a ha; simp [p1722] at ha; subst a; trivial
  · exact checked1722
theorem derived1722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1722 := by
  apply localUnsat_implies_entails f1722 [c1489, c1621, c1721, c379, c53, c1287, c385, c341, c147, c188, c839, c1118, c201, c171, c1117] c1722 unsat1722 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c839 := derived839 a h
  have h11 : Entails.eval a c1118 := derived1118 a h
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c1117 := derived1117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1723 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1721, some c1621, some c1722, some c379, some c53, some c1287, some c43, some c108, some c109, some c82, some c1704, some c1586, some c384, some c307, some c342, some c77, some c809, some c225, some c30, some c28, some c216, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1723 : lratChecker f1723 p1723 = .success := by decide +kernel
theorem unsat1723 : Unsatisfiable (PosFin 57) f1723 := by
  apply lratCheckerSound f1723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1723
  · intro a ha; simp [p1723] at ha; subst a; trivial
  · exact checked1723
theorem derived1723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1723 := by
  apply localUnsat_implies_entails f1723 [c1489, c1721, c1621, c1722, c379, c53, c1287, c43, c108, c109, c82, c1704, c1586, c384, c307, c342, c77, c809, c225, c30, c28, c216] c1723 unsat1723 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1722 := derived1722 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c1704 := derived1704 a h
  have h12 : Entails.eval a c1586 := derived1586 a h
  have h13 : Entails.eval a c384 := h 383 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c342 := h 341 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c809 := derived809 a h
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c30 := h 29 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1724 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1722, some c1723, some c327, some c42, some c1511, some c112, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1724 : lratChecker f1724 p1724 = .success := by decide +kernel
theorem unsat1724 : Unsatisfiable (PosFin 57) f1724 := by
  apply lratCheckerSound f1724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1724
  · intro a ha; simp [p1724] at ha; subst a; trivial
  · exact checked1724
theorem derived1724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1724 := by
  apply localUnsat_implies_entails f1724 [c1489, c1722, c1723, c327, c42, c1511, c112] c1724 unsat1724 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1722 := derived1722 a h
  have h2 : Entails.eval a c1723 := derived1723 a h
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c1511 := derived1511 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1725 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c379, some c41, some c81, some c300, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1725 : lratChecker f1725 p1725 = .success := by decide +kernel
theorem unsat1725 : Unsatisfiable (PosFin 57) f1725 := by
  apply lratCheckerSound f1725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1725
  · intro a ha; simp [p1725] at ha; subst a; trivial
  · exact checked1725
theorem derived1725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1725 := by
  apply localUnsat_implies_entails f1725 [c1721, c1489, c379, c41, c81, c300] c1725 unsat1725 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1726 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1722, some c379, some c53, some c1287, some c1586, some c1045, some c342, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1726 : lratChecker f1726 p1726 = .success := by decide +kernel
theorem unsat1726 : Unsatisfiable (PosFin 57) f1726 := by
  apply lratCheckerSound f1726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1726
  · intro a ha; simp [p1726] at ha; subst a; trivial
  · exact checked1726
theorem derived1726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1726 := by
  apply localUnsat_implies_entails f1726 [c1721, c1489, c1722, c379, c53, c1287, c1586, c1045, c342] c1726 unsat1726 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1722 := derived1722 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c1586 := derived1586 a h
  have h7 : Entails.eval a c1045 := derived1045 a h
  have h8 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1727 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1621, some c1722, some c379, some c53, some c1287, some c1725, some c1724, some c37, some c1652, some c1660, some c112, some c343, some c119, some c1726, some c1592, some c110, some c109, some c986, some c1683, some c388, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1727 : lratChecker f1727 p1727 = .success := by decide +kernel
theorem unsat1727 : Unsatisfiable (PosFin 57) f1727 := by
  apply lratCheckerSound f1727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1727
  · intro a ha; simp [p1727] at ha; subst a; trivial
  · exact checked1727
theorem derived1727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1727 := by
  apply localUnsat_implies_entails f1727 [c1721, c1489, c1621, c1722, c379, c53, c1287, c1725, c1724, c37, c1652, c1660, c112, c343, c119, c1726, c1592, c110, c109, c986, c1683, c388] c1727 unsat1727 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1722 := derived1722 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1287 := derived1287 a h
  have h7 : Entails.eval a c1725 := derived1725 a h
  have h8 : Entails.eval a c1724 := derived1724 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c1652 := derived1652 a h
  have h11 : Entails.eval a c1660 := derived1660 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c1726 := derived1726 a h
  have h16 : Entails.eval a c1592 := derived1592 a h
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c986 := derived986 a h
  have h20 : Entails.eval a c1683 := derived1683 a h
  have h21 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1728 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1621, some c1287, some c379, some c53, some c1722, some c1727, some c1215, some c1173, some c119, some c147, some c255, some c343, some c113, some c202, some c160, some c172, some c983, some c342, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1728 : lratChecker f1728 p1728 = .success := by decide +kernel
theorem unsat1728 : Unsatisfiable (PosFin 57) f1728 := by
  apply lratCheckerSound f1728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1728
  · intro a ha; simp [p1728] at ha; subst a; trivial
  · exact checked1728
theorem derived1728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1728 := by
  apply localUnsat_implies_entails f1728 [c1721, c1489, c1621, c1287, c379, c53, c1722, c1727, c1215, c1173, c119, c147, c255, c343, c113, c202, c160, c172, c983, c342] c1728 unsat1728 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1722 := derived1722 a h
  have h7 : Entails.eval a c1727 := derived1727 a h
  have h8 : Entails.eval a c1215 := derived1215 a h
  have h9 : Entails.eval a c1173 := derived1173 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c983 := derived983 a h
  have h19 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1729 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1222, some c1216, some c183, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p1729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1729 : lratChecker f1729 p1729 = .success := by decide +kernel
theorem unsat1729 : Unsatisfiable (PosFin 57) f1729 := by
  apply lratCheckerSound f1729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1729
  · intro a ha; simp [p1729] at ha; subst a; trivial
  · exact checked1729
theorem derived1729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1729 := by
  apply localUnsat_implies_entails f1729 [c1721, c1222, c1216, c183] c1729 unsat1729 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1222 := derived1222 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1730 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨44, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, true), (⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1287, some c385, some c316, some c1632, some c1179, some c305, some c78, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1730 : lratChecker f1730 p1730 = .success := by decide +kernel
theorem unsat1730 : Unsatisfiable (PosFin 57) f1730 := by
  apply lratCheckerSound f1730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1730
  · intro a ha; simp [p1730] at ha; subst a; trivial
  · exact checked1730
theorem derived1730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1730 := by
  apply localUnsat_implies_entails f1730 [c1621, c1287, c385, c316, c1632, c1179, c305, c78] c1730 unsat1730 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c316 := h 315 (by decide)
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c1179 := derived1179 a h
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1731 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1489, some c1721, some c1728, some c1211, some c1287, some c385, some c147, some c16, some c1729, some c391, some c316, some c1062, some c1223, some c1730, some c1592, some c41, some c324, some c298, some c42, some c81, some c112, some c377, some c84, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1731 : lratChecker f1731 p1731 = .success := by decide +kernel
theorem unsat1731 : Unsatisfiable (PosFin 57) f1731 := by
  apply lratCheckerSound f1731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1731
  · intro a ha; simp [p1731] at ha; subst a; trivial
  · exact checked1731
theorem derived1731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1731 := by
  apply localUnsat_implies_entails f1731 [c1621, c1489, c1721, c1728, c1211, c1287, c385, c147, c16, c1729, c391, c316, c1062, c1223, c1730, c1592, c41, c324, c298, c42, c81, c112, c377, c84] c1731 unsat1731 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c1728 := derived1728 a h
  have h4 : Entails.eval a c1211 := derived1211 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c1729 := derived1729 a h
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c1062 := derived1062 a h
  have h13 : Entails.eval a c1223 := derived1223 a h
  have h14 : Entails.eval a c1730 := derived1730 a h
  have h15 : Entails.eval a c1592 := derived1592 a h
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c324 := h 323 (by decide)
  have h18 : Entails.eval a c298 := h 297 (by decide)
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  have h21 : Entails.eval a c112 := h 111 (by decide)
  have h22 : Entails.eval a c377 := h 376 (by decide)
  have h23 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1732 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨48, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1721, some c1211, some c1224, some c1046, some c119, some c16, some c186, some c1218, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1732 : lratChecker f1732 p1732 = .success := by decide +kernel
theorem unsat1732 : Unsatisfiable (PosFin 57) f1732 := by
  apply lratCheckerSound f1732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1732
  · intro a ha; simp [p1732] at ha; subst a; trivial
  · exact checked1732
theorem derived1732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1732 := by
  apply localUnsat_implies_entails f1732 [c1621, c1721, c1211, c1224, c1046, c119, c16, c186, c1218] c1732 unsat1732 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1211 := derived1211 a h
  have h3 : Entails.eval a c1224 := derived1224 a h
  have h4 : Entails.eval a c1046 := derived1046 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c1218 := derived1218 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1733 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1287, some c1728, some c1732, some c385, some c1731, some c147, some c1173, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1733 : lratChecker f1733 p1733 = .success := by decide +kernel
theorem unsat1733 : Unsatisfiable (PosFin 57) f1733 := by
  apply lratCheckerSound f1733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1733
  · intro a ha; simp [p1733] at ha; subst a; trivial
  · exact checked1733
theorem derived1733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1733 := by
  apply localUnsat_implies_entails f1733 [c1621, c1287, c1728, c1732, c385, c1731, c147, c1173] c1733 unsat1733 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1287 := derived1287 a h
  have h2 : Entails.eval a c1728 := derived1728 a h
  have h3 : Entails.eval a c1732 := derived1732 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c1731 := derived1731 a h
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c1173 := derived1173 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1734 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1621, some c379, some c52, some c1704, some c307, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1734 : lratChecker f1734 p1734 = .success := by decide +kernel
theorem unsat1734 : Unsatisfiable (PosFin 57) f1734 := by
  apply lratCheckerSound f1734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1734
  · intro a ha; simp [p1734] at ha; subst a; trivial
  · exact checked1734
theorem derived1734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1734 := by
  apply localUnsat_implies_entails f1734 [c1721, c1621, c379, c52, c1704, c307] c1734 unsat1734 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c1704 := derived1704 a h
  have h5 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1735 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1721, some c1733, some c1287, some c39, some c379, some c53, some c343, some c1725, some c1734, some c109, some c68, some c83, some c43, some c385, some c110, some c1214, some c1326, some c42, some c304, some c288, some c225, some c26, some c210, some c115, some c255, some c10, some c119, some c1218, some c188, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1735 : lratChecker f1735 p1735 = .success := by decide +kernel
theorem unsat1735 : Unsatisfiable (PosFin 57) f1735 := by
  apply lratCheckerSound f1735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1735
  · intro a ha; simp [p1735] at ha; subst a; trivial
  · exact checked1735
theorem derived1735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1735 := by
  apply localUnsat_implies_entails f1735 [c1489, c1621, c1721, c1733, c1287, c39, c379, c53, c343, c1725, c1734, c109, c68, c83, c43, c385, c110, c1214, c1326, c42, c304, c288, c225, c26, c210, c115, c255, c10, c119, c1218, c188] c1735 unsat1735 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c1733 := derived1733 a h
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c1725 := derived1725 a h
  have h10 : Entails.eval a c1734 := derived1734 a h
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  have h15 : Entails.eval a c385 := h 384 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c1214 := derived1214 a h
  have h18 : Entails.eval a c1326 := derived1326 a h
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c304 := h 303 (by decide)
  have h21 : Entails.eval a c288 := h 287 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  have h23 : Entails.eval a c26 := h 25 (by decide)
  have h24 : Entails.eval a c210 := h 209 (by decide)
  have h25 : Entails.eval a c115 := h 114 (by decide)
  have h26 : Entails.eval a c255 := h 254 (by decide)
  have h27 : Entails.eval a c10 := h 9 (by decide)
  have h28 : Entails.eval a c119 := h 118 (by decide)
  have h29 : Entails.eval a c1218 := derived1218 a h
  have h30 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1736 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨36, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c145, some c1214, some c324, some c301, some c285, some c312, some c82, some c223, some c389, some c388, some c346, some c10, some c21, some c318, some c370, some c772, some c1328, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p1736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1736 : lratChecker f1736 p1736 = .success := by decide +kernel
theorem unsat1736 : Unsatisfiable (PosFin 57) f1736 := by
  apply lratCheckerSound f1736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1736
  · intro a ha; simp [p1736] at ha; subst a; trivial
  · exact checked1736
theorem derived1736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1736 := by
  apply localUnsat_implies_entails f1736 [c1489, c145, c1214, c324, c301, c285, c312, c82, c223, c389, c388, c346, c10, c21, c318, c370, c772, c1328] c1736 unsat1736 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c1214 := derived1214 a h
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c346 := h 345 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c772 := derived772 a h
  have h17 : Entails.eval a c1328 := derived1328 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1737 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1621, some c1287, some c1733, some c39, some c379, some c53, some c343, some c385, some c1725, some c1734, some c1592, some c110, some c109, some c1214, some c43, some c83, some c68, some c1735, some c145, some c1736, some c42, some c10, some c143, some c150, some c115, some c201, some c263, some c119, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1737 : lratChecker f1737 p1737 = .success := by decide +kernel
theorem unsat1737 : Unsatisfiable (PosFin 57) f1737 := by
  apply lratCheckerSound f1737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1737
  · intro a ha; simp [p1737] at ha; subst a; trivial
  · exact checked1737
theorem derived1737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1737 := by
  apply localUnsat_implies_entails f1737 [c1721, c1489, c1621, c1287, c1733, c39, c379, c53, c343, c385, c1725, c1734, c1592, c110, c109, c1214, c43, c83, c68, c1735, c145, c1736, c42, c10, c143, c150, c115, c201, c263, c119] c1737 unsat1737 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1733 := derived1733 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c1725 := derived1725 a h
  have h11 : Entails.eval a c1734 := derived1734 a h
  have h12 : Entails.eval a c1592 := derived1592 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  have h15 : Entails.eval a c1214 := derived1214 a h
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c83 := h 82 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  have h19 : Entails.eval a c1735 := derived1735 a h
  have h20 : Entails.eval a c145 := h 144 (by decide)
  have h21 : Entails.eval a c1736 := derived1736 a h
  have h22 : Entails.eval a c42 := h 41 (by decide)
  have h23 : Entails.eval a c10 := h 9 (by decide)
  have h24 : Entails.eval a c143 := h 142 (by decide)
  have h25 : Entails.eval a c150 := h 149 (by decide)
  have h26 : Entails.eval a c115 := h 114 (by decide)
  have h27 : Entails.eval a c201 := h 200 (by decide)
  have h28 : Entails.eval a c263 := h 262 (by decide)
  have h29 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1738 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1721, some c1621, some c1287, some c1733, some c39, some c385, some c379, some c53, some c343, some c1737, some c1215, some c188, some c119, some c255, some c113, some c202, some c160, some c172, some c983, some c342, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1738 : lratChecker f1738 p1738 = .success := by decide +kernel
theorem unsat1738 : Unsatisfiable (PosFin 57) f1738 := by
  apply lratCheckerSound f1738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1738
  · intro a ha; simp [p1738] at ha; subst a; trivial
  · exact checked1738
theorem derived1738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1738 := by
  apply localUnsat_implies_entails f1738 [c1489, c1721, c1621, c1287, c1733, c39, c385, c379, c53, c343, c1737, c1215, c188, c119, c255, c113, c202, c160, c172, c983, c342] c1738 unsat1738 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1733 := derived1733 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c1737 := derived1737 a h
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c255 := h 254 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c983 := derived983 a h
  have h20 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1739 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1621, some c1489, some c1287, some c1733, some c39, some c385, some c1738, some c1224, some c377, some c384, some c82, some c1211, some c110, some c108, some c52, some c1704, some c43, some c83, some c305, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1739 : lratChecker f1739 p1739 = .success := by decide +kernel
theorem unsat1739 : Unsatisfiable (PosFin 57) f1739 := by
  apply lratCheckerSound f1739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1739
  · intro a ha; simp [p1739] at ha; subst a; trivial
  · exact checked1739
theorem derived1739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1739 := by
  apply localUnsat_implies_entails f1739 [c1721, c1621, c1489, c1287, c1733, c39, c385, c1738, c1224, c377, c384, c82, c1211, c110, c108, c52, c1704, c43, c83, c305] c1739 unsat1739 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1733 := derived1733 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1224 := derived1224 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c1211 := derived1211 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c52 := h 51 (by decide)
  have h16 : Entails.eval a c1704 := derived1704 a h
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  have h19 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1740 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1621, some c1733, some c1287, some c39, some c385, some c1738, some c1224, some c377, some c53, some c343, some c1739, some c65, some c41, some c384, some c1222, some c1211, some c326, some c284, some c52, some c228, some c335, some c31, some c281, some c220, some c214, some c263, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1740 : lratChecker f1740 p1740 = .success := by decide +kernel
theorem unsat1740 : Unsatisfiable (PosFin 57) f1740 := by
  apply lratCheckerSound f1740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1740
  · intro a ha; simp [p1740] at ha; subst a; trivial
  · exact checked1740
theorem derived1740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1740 := by
  apply localUnsat_implies_entails f1740 [c1721, c1489, c1621, c1733, c1287, c39, c385, c1738, c1224, c377, c53, c343, c1739, c65, c41, c384, c1222, c1211, c326, c284, c52, c228, c335, c31, c281, c220, c214, c263] c1740 unsat1740 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1733 := derived1733 a h
  have h4 : Entails.eval a c1287 := derived1287 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1224 := derived1224 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  have h12 : Entails.eval a c1739 := derived1739 a h
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c384 := h 383 (by decide)
  have h16 : Entails.eval a c1222 := derived1222 a h
  have h17 : Entails.eval a c1211 := derived1211 a h
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c52 := h 51 (by decide)
  have h21 : Entails.eval a c228 := h 227 (by decide)
  have h22 : Entails.eval a c335 := h 334 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c281 := h 280 (by decide)
  have h25 : Entails.eval a c220 := h 219 (by decide)
  have h26 : Entails.eval a c214 := h 213 (by decide)
  have h27 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1741 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1721, some c1489, some c1287, some c1733, some c39, some c385, some c1738, some c1224, some c377, some c384, some c1222, some c82, some c1739, some c1740, some c1221, some c976, some c388, some c96, some c111, some c43, some c83, some c304, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1741 : lratChecker f1741 p1741 = .success := by decide +kernel
theorem unsat1741 : Unsatisfiable (PosFin 57) f1741 := by
  apply lratCheckerSound f1741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1741
  · intro a ha; simp [p1741] at ha; subst a; trivial
  · exact checked1741
theorem derived1741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1741 := by
  apply localUnsat_implies_entails f1741 [c1621, c1721, c1489, c1287, c1733, c39, c385, c1738, c1224, c377, c384, c1222, c82, c1739, c1740, c1221, c976, c388, c96, c111, c43, c83, c304] c1741 unsat1741 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1287 := derived1287 a h
  have h4 : Entails.eval a c1733 := derived1733 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1224 := derived1224 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c1222 := derived1222 a h
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c1739 := derived1739 a h
  have h14 : Entails.eval a c1740 := derived1740 a h
  have h15 : Entails.eval a c1221 := derived1221 a h
  have h16 : Entails.eval a c976 := derived976 a h
  have h17 : Entails.eval a c388 := h 387 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c83 := h 82 (by decide)
  have h22 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1742 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1621, some c1721, some c379, some c53, some c73, some c385, some c341, some c147, some c188, some c171, some c14, some c186, some c57, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1742 : lratChecker f1742 p1742 = .success := by decide +kernel
theorem unsat1742 : Unsatisfiable (PosFin 57) f1742 := by
  apply lratCheckerSound f1742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1742
  · intro a ha; simp [p1742] at ha; subst a; trivial
  · exact checked1742
theorem derived1742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1742 := by
  apply localUnsat_implies_entails f1742 [c1489, c1621, c1721, c379, c53, c73, c385, c341, c147, c188, c171, c14, c186, c57] c1742 unsat1742 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1743 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨53, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c188, some c1218, some c14, some c186, some c77, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1743 : lratChecker f1743 p1743 = .success := by decide +kernel
theorem unsat1743 : Unsatisfiable (PosFin 57) f1743 := by
  apply lratCheckerSound f1743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1743
  · intro a ha; simp [p1743] at ha; subst a; trivial
  · exact checked1743
theorem derived1743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1743 := by
  apply localUnsat_implies_entails f1743 [c1721, c188, c1218, c14, c186, c77] c1743 unsat1743 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c188 := h 187 (by decide)
  have h2 : Entails.eval a c1218 := derived1218 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1744 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1621, some c1741, some c379, some c73, some c53, some c997, some c342, some c322, some c280, some c1742, some c1743, some c119, some c147, some c160, some c255, some c343, some c1040, some c1034, some c263, some c986, some c32, some c15, some c128, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1744 : lratChecker f1744 p1744 = .success := by decide +kernel
theorem unsat1744 : Unsatisfiable (PosFin 57) f1744 := by
  apply lratCheckerSound f1744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1744
  · intro a ha; simp [p1744] at ha; subst a; trivial
  · exact checked1744
theorem derived1744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1744 := by
  apply localUnsat_implies_entails f1744 [c1721, c1489, c1621, c1741, c379, c73, c53, c997, c342, c322, c280, c1742, c1743, c119, c147, c160, c255, c343, c1040, c1034, c263, c986, c32, c15, c128] c1744 unsat1744 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1741 := derived1741 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c997 := derived997 a h
  have h8 : Entails.eval a c342 := h 341 (by decide)
  have h9 : Entails.eval a c322 := h 321 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c1742 := derived1742 a h
  have h12 : Entails.eval a c1743 := derived1743 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c255 := h 254 (by decide)
  have h17 : Entails.eval a c343 := h 342 (by decide)
  have h18 : Entails.eval a c1040 := derived1040 a h
  have h19 : Entails.eval a c1034 := derived1034 a h
  have h20 : Entails.eval a c263 := h 262 (by decide)
  have h21 : Entails.eval a c986 := derived986 a h
  have h22 : Entails.eval a c32 := h 31 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1745 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1721, some c1621, some c1741, some c379, some c73, some c53, some c997, some c342, some c1744, some c1210, some c1215, some c1173, some c119, some c147, some c385, some c343, some c1040, some c172, some c15, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1745 : lratChecker f1745 p1745 = .success := by decide +kernel
theorem unsat1745 : Unsatisfiable (PosFin 57) f1745 := by
  apply lratCheckerSound f1745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1745
  · intro a ha; simp [p1745] at ha; subst a; trivial
  · exact checked1745
theorem derived1745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1745 := by
  apply localUnsat_implies_entails f1745 [c1489, c1721, c1621, c1741, c379, c73, c53, c997, c342, c1744, c1210, c1215, c1173, c119, c147, c385, c343, c1040, c172, c15] c1745 unsat1745 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1741 := derived1741 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c997 := derived997 a h
  have h8 : Entails.eval a c342 := h 341 (by decide)
  have h9 : Entails.eval a c1744 := derived1744 a h
  have h10 : Entails.eval a c1210 := derived1210 a h
  have h11 : Entails.eval a c1215 := derived1215 a h
  have h12 : Entails.eval a c1173 := derived1173 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c385 := h 384 (by decide)
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c1040 := derived1040 a h
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1746 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨49, by decide⟩, false), (⟨15, by decide⟩, false), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c1721, some c1745, some c1211, some c16, some c1729, some c1732, some c341, some c280, some c339, some c1076, some c186, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1746 : lratChecker f1746 p1746 = .success := by decide +kernel
theorem unsat1746 : Unsatisfiable (PosFin 57) f1746 := by
  apply lratCheckerSound f1746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1746
  · intro a ha; simp [p1746] at ha; subst a; trivial
  · exact checked1746
theorem derived1746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1746 := by
  apply localUnsat_implies_entails f1746 [c1741, c1721, c1745, c1211, c16, c1729, c1732, c341, c280, c339, c1076, c186] c1746 unsat1746 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1745 := derived1745 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1729 := derived1729 a h
  have h6 : Entails.eval a c1732 := derived1732 a h
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c1076 := derived1076 a h
  have h11 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1747 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨55, by decide⟩, true), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c1489, some c1721, some c1621, some c974, some c147, some c322, some c1745, some c1732, some c1211, some c1746, some c53, some c840, some c377, some c253, some c254, some c251, some c220, some c32, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1747 : lratChecker f1747 p1747 = .success := by decide +kernel
theorem unsat1747 : Unsatisfiable (PosFin 57) f1747 := by
  apply lratCheckerSound f1747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1747
  · intro a ha; simp [p1747] at ha; subst a; trivial
  · exact checked1747
theorem derived1747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1747 := by
  apply localUnsat_implies_entails f1747 [c1741, c1489, c1721, c1621, c974, c147, c322, c1745, c1732, c1211, c1746, c53, c840, c377, c253, c254, c251, c220, c32] c1747 unsat1747 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c1621 := derived1621 a h
  have h4 : Entails.eval a c974 := derived974 a h
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c1745 := derived1745 a h
  have h8 : Entails.eval a c1732 := derived1732 a h
  have h9 : Entails.eval a c1211 := derived1211 a h
  have h10 : Entails.eval a c1746 := derived1746 a h
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c840 := derived840 a h
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c253 := h 252 (by decide)
  have h15 : Entails.eval a c254 := h 253 (by decide)
  have h16 : Entails.eval a c251 := h 250 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1748 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨32, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1741, some c1489, some c1721, some c322, some c1745, some c1732, some c1211, some c147, some c974, some c16, some c1729, some c391, some c1062, some c1223, some c1632, some c110, some c1747, some c73, some c95, some c93, some c377, some c13, some c118, some c1532, some c31, some c247, some c251, some c262, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1748 : lratChecker f1748 p1748 = .success := by decide +kernel
theorem unsat1748 : Unsatisfiable (PosFin 57) f1748 := by
  apply lratCheckerSound f1748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1748
  · intro a ha; simp [p1748] at ha; subst a; trivial
  · exact checked1748
theorem derived1748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1748 := by
  apply localUnsat_implies_entails f1748 [c1621, c1741, c1489, c1721, c322, c1745, c1732, c1211, c147, c974, c16, c1729, c391, c1062, c1223, c1632, c110, c1747, c73, c95, c93, c377, c13, c118, c1532, c31, c247, c251, c262] c1748 unsat1748 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1741 := derived1741 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c1745 := derived1745 a h
  have h6 : Entails.eval a c1732 := derived1732 a h
  have h7 : Entails.eval a c1211 := derived1211 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c974 := derived974 a h
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c1729 := derived1729 a h
  have h12 : Entails.eval a c391 := h 390 (by decide)
  have h13 : Entails.eval a c1062 := derived1062 a h
  have h14 : Entails.eval a c1223 := derived1223 a h
  have h15 : Entails.eval a c1632 := derived1632 a h
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c1747 := derived1747 a h
  have h18 : Entails.eval a c73 := h 72 (by decide)
  have h19 : Entails.eval a c95 := h 94 (by decide)
  have h20 : Entails.eval a c93 := h 92 (by decide)
  have h21 : Entails.eval a c377 := h 376 (by decide)
  have h22 : Entails.eval a c13 := h 12 (by decide)
  have h23 : Entails.eval a c118 := h 117 (by decide)
  have h24 : Entails.eval a c1532 := derived1532 a h
  have h25 : Entails.eval a c31 := h 30 (by decide)
  have h26 : Entails.eval a c247 := h 246 (by decide)
  have h27 : Entails.eval a c251 := h 250 (by decide)
  have h28 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1749 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1745, some c1211, some c16, some c1729, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1749 : lratChecker f1749 p1749 = .success := by decide +kernel
theorem unsat1749 : Unsatisfiable (PosFin 57) f1749 := by
  apply lratCheckerSound f1749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1749
  · intro a ha; simp [p1749] at ha; subst a; trivial
  · exact checked1749
theorem derived1749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1749 := by
  apply localUnsat_implies_entails f1749 [c1745, c1211, c16, c1729] c1749 unsat1749 (by rfl) a
  have h0 : Entails.eval a c1745 := derived1745 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c1729 := derived1729 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1750 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1721, some c1621, some c1745, some c1732, some c1211, some c385, some c392, some c73, some c377, some c1749, some c119, some c32, some c266, some c251, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1750 : lratChecker f1750 p1750 = .success := by decide +kernel
theorem unsat1750 : Unsatisfiable (PosFin 57) f1750 := by
  apply lratCheckerSound f1750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1750
  · intro a ha; simp [p1750] at ha; subst a; trivial
  · exact checked1750
theorem derived1750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1750 := by
  apply localUnsat_implies_entails f1750 [c1489, c1721, c1621, c1745, c1732, c1211, c385, c392, c73, c377, c1749, c119, c32, c266, c251] c1750 unsat1750 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1745 := derived1745 a h
  have h4 : Entails.eval a c1732 := derived1732 a h
  have h5 : Entails.eval a c1211 := derived1211 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c1749 := derived1749 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1751 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1750, some c147, some c1748, some c1173, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1751 : lratChecker f1751 p1751 = .success := by decide +kernel
theorem unsat1751 : Unsatisfiable (PosFin 57) f1751 := by
  apply lratCheckerSound f1751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1751
  · intro a ha; simp [p1751] at ha; subst a; trivial
  · exact checked1751
theorem derived1751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1751 := by
  apply localUnsat_implies_entails f1751 [c1621, c1750, c147, c1748, c1173] c1751 unsat1751 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1750 := derived1750 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c1748 := derived1748 a h
  have h4 : Entails.eval a c1173 := derived1173 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1752 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1751, some c1621, some c39, some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1752 : lratChecker f1752 p1752 = .success := by decide +kernel
theorem unsat1752 : Unsatisfiable (PosFin 57) f1752 := by
  apply lratCheckerSound f1752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1752
  · intro a ha; simp [p1752] at ha; subst a; trivial
  · exact checked1752
theorem derived1752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1752 := by
  apply localUnsat_implies_entails f1752 [c1751, c1621, c39] c1752 unsat1752 (by rfl) a
  have h0 : Entails.eval a c1751 := derived1751 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1753 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1621, some c1751, some c1752, some c1741, some c1489, some c1721, some c379, some c53, some c280, some c73, some c343, some c997, some c342, some c72, some c1029, some c109, some c110, some c69, some c1592, some c385, some c188, some c1218, some c208, some c1216, some c167, some c349, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1753 : lratChecker f1753 p1753 = .success := by decide +kernel
theorem unsat1753 : Unsatisfiable (PosFin 57) f1753 := by
  apply lratCheckerSound f1753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1753
  · intro a ha; simp [p1753] at ha; subst a; trivial
  · exact checked1753
theorem derived1753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1753 := by
  apply localUnsat_implies_entails f1753 [c1621, c1751, c1752, c1741, c1489, c1721, c379, c53, c280, c73, c343, c997, c342, c72, c1029, c109, c110, c69, c1592, c385, c188, c1218, c208, c1216, c167, c349] c1753 unsat1753 (by rfl) a
  have h0 : Entails.eval a c1621 := derived1621 a h
  have h1 : Entails.eval a c1751 := derived1751 a h
  have h2 : Entails.eval a c1752 := derived1752 a h
  have h3 : Entails.eval a c1741 := derived1741 a h
  have h4 : Entails.eval a c1489 := derived1489 a h
  have h5 : Entails.eval a c1721 := derived1721 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c997 := derived997 a h
  have h12 : Entails.eval a c342 := h 341 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c1029 := derived1029 a h
  have h15 : Entails.eval a c109 := h 108 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c1592 := derived1592 a h
  have h19 : Entails.eval a c385 := h 384 (by decide)
  have h20 : Entails.eval a c188 := h 187 (by decide)
  have h21 : Entails.eval a c1218 := derived1218 a h
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c1216 := derived1216 a h
  have h24 : Entails.eval a c167 := h 166 (by decide)
  have h25 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1754 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1751, some c1489, some c1752, some c1741, some c1621, some c379, some c73, some c53, some c343, some c997, some c342, some c72, some c385, some c322, some c1029, some c280, some c110, some c109, some c1390, some c1753, some c119, some c160, some c255, some c1034, some c7, some c21, some c153, some c241, some c300, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1754 : lratChecker f1754 p1754 = .success := by decide +kernel
theorem unsat1754 : Unsatisfiable (PosFin 57) f1754 := by
  apply lratCheckerSound f1754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1754
  · intro a ha; simp [p1754] at ha; subst a; trivial
  · exact checked1754
theorem derived1754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1754 := by
  apply localUnsat_implies_entails f1754 [c1721, c1751, c1489, c1752, c1741, c1621, c379, c73, c53, c343, c997, c342, c72, c385, c322, c1029, c280, c110, c109, c1390, c1753, c119, c160, c255, c1034, c7, c21, c153, c241, c300] c1754 unsat1754 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1751 := derived1751 a h
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c1752 := derived1752 a h
  have h4 : Entails.eval a c1741 := derived1741 a h
  have h5 : Entails.eval a c1621 := derived1621 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c997 := derived997 a h
  have h11 : Entails.eval a c342 := h 341 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c385 := h 384 (by decide)
  have h14 : Entails.eval a c322 := h 321 (by decide)
  have h15 : Entails.eval a c1029 := derived1029 a h
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c1390 := derived1390 a h
  have h20 : Entails.eval a c1753 := derived1753 a h
  have h21 : Entails.eval a c119 := h 118 (by decide)
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c255 := h 254 (by decide)
  have h24 : Entails.eval a c1034 := derived1034 a h
  have h25 : Entails.eval a c7 := h 6 (by decide)
  have h26 : Entails.eval a c21 := h 20 (by decide)
  have h27 : Entails.eval a c153 := h 152 (by decide)
  have h28 : Entails.eval a c241 := h 240 (by decide)
  have h29 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1755 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1741, some c1621, some c1752, some c1751, some c1721, some c379, some c73, some c53, some c997, some c342, some c343, some c72, some c1754, some c1210, some c1215, some c188, some c15, some c172, some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p1755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1755 : lratChecker f1755 p1755 = .success := by decide +kernel
theorem unsat1755 : Unsatisfiable (PosFin 57) f1755 := by
  apply lratCheckerSound f1755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1755
  · intro a ha; simp [p1755] at ha; subst a; trivial
  · exact checked1755
theorem derived1755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1755 := by
  apply localUnsat_implies_entails f1755 [c1489, c1741, c1621, c1752, c1751, c1721, c379, c73, c53, c997, c342, c343, c72, c1754, c1210, c1215, c188, c15, c172] c1755 unsat1755 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1741 := derived1741 a h
  have h2 : Entails.eval a c1621 := derived1621 a h
  have h3 : Entails.eval a c1752 := derived1752 a h
  have h4 : Entails.eval a c1751 := derived1751 a h
  have h5 : Entails.eval a c1721 := derived1721 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c997 := derived997 a h
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c1754 := derived1754 a h
  have h14 : Entails.eval a c1210 := derived1210 a h
  have h15 : Entails.eval a c1215 := derived1215 a h
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1756 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1755, some c1211, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1756 : lratChecker f1756 p1756 = .success := by decide +kernel
theorem unsat1756 : Unsatisfiable (PosFin 57) f1756 := by
  apply lratCheckerSound f1756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1756
  · intro a ha; simp [p1756] at ha; subst a; trivial
  · exact checked1756
theorem derived1756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1756 := by
  apply localUnsat_implies_entails f1756 [c1755, c1211] c1756 unsat1756 (by rfl) a
  have h0 : Entails.eval a c1755 := derived1755 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1757 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1752, some c1755, some c1721, some c392, some c1222, some c385, some c73, some c175, some c183, some c190, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1757 : lratChecker f1757 p1757 = .success := by decide +kernel
theorem unsat1757 : Unsatisfiable (PosFin 57) f1757 := by
  apply lratCheckerSound f1757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1757
  · intro a ha; simp [p1757] at ha; subst a; trivial
  · exact checked1757
theorem derived1757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1757 := by
  apply localUnsat_implies_entails f1757 [c1489, c1752, c1755, c1721, c392, c1222, c385, c73, c175, c183, c190] c1757 unsat1757 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1752 := derived1752 a h
  have h2 : Entails.eval a c1755 := derived1755 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c392 := h 391 (by decide)
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c385 := h 384 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1758 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1751, some c1489, some c1721, some c1621, some c1752, some c1755, some c1756, some c1741, some c1340, some c322, some c385, some c73, some c377, some c1757, some c119, some c160, some c266, some c225, some c251, some c31, some c271, some c218, some c250, some c277, some c174, some c121, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1758 : lratChecker f1758 p1758 = .success := by decide +kernel
theorem unsat1758 : Unsatisfiable (PosFin 57) f1758 := by
  apply lratCheckerSound f1758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1758
  · intro a ha; simp [p1758] at ha; subst a; trivial
  · exact checked1758
theorem derived1758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1758 := by
  apply localUnsat_implies_entails f1758 [c1751, c1489, c1721, c1621, c1752, c1755, c1756, c1741, c1340, c322, c385, c73, c377, c1757, c119, c160, c266, c225, c251, c31, c271, c218, c250, c277, c174, c121] c1758 unsat1758 (by rfl) a
  have h0 : Entails.eval a c1751 := derived1751 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c1621 := derived1621 a h
  have h4 : Entails.eval a c1752 := derived1752 a h
  have h5 : Entails.eval a c1755 := derived1755 a h
  have h6 : Entails.eval a c1756 := derived1756 a h
  have h7 : Entails.eval a c1741 := derived1741 a h
  have h8 : Entails.eval a c1340 := derived1340 a h
  have h9 : Entails.eval a c322 := h 321 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c1757 := derived1757 a h
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  have h17 : Entails.eval a c225 := h 224 (by decide)
  have h18 : Entails.eval a c251 := h 250 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c218 := h 217 (by decide)
  have h22 : Entails.eval a c250 := h 249 (by decide)
  have h23 : Entails.eval a c277 := h 276 (by decide)
  have h24 : Entails.eval a c174 := h 173 (by decide)
  have h25 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1759 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1721, some c1489, some c1741, some c1751, some c1755, some c1756, some c1621, some c1752, some c322, some c1340, some c110, some c45, some c1758, some c1224, some c377, some c384, some c73, some c53, some c1222, some c343, some c280, some c65, some c228, some c335, some c31, some c281, some c220, some c214, some c263, some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1759 : lratChecker f1759 p1759 = .success := by decide +kernel
theorem unsat1759 : Unsatisfiable (PosFin 57) f1759 := by
  apply lratCheckerSound f1759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1759
  · intro a ha; simp [p1759] at ha; subst a; trivial
  · exact checked1759
theorem derived1759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1759 := by
  apply localUnsat_implies_entails f1759 [c1721, c1489, c1741, c1751, c1755, c1756, c1621, c1752, c322, c1340, c110, c45, c1758, c1224, c377, c384, c73, c53, c1222, c343, c280, c65, c228, c335, c31, c281, c220, c214, c263] c1759 unsat1759 (by rfl) a
  have h0 : Entails.eval a c1721 := derived1721 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c1741 := derived1741 a h
  have h3 : Entails.eval a c1751 := derived1751 a h
  have h4 : Entails.eval a c1755 := derived1755 a h
  have h5 : Entails.eval a c1756 := derived1756 a h
  have h6 : Entails.eval a c1621 := derived1621 a h
  have h7 : Entails.eval a c1752 := derived1752 a h
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c1340 := derived1340 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c1758 := derived1758 a h
  have h13 : Entails.eval a c1224 := derived1224 a h
  have h14 : Entails.eval a c377 := h 376 (by decide)
  have h15 : Entails.eval a c384 := h 383 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  have h18 : Entails.eval a c1222 := derived1222 a h
  have h19 : Entails.eval a c343 := h 342 (by decide)
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c65 := h 64 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  have h23 : Entails.eval a c335 := h 334 (by decide)
  have h24 : Entails.eval a c31 := h 30 (by decide)
  have h25 : Entails.eval a c281 := h 280 (by decide)
  have h26 : Entails.eval a c220 := h 219 (by decide)
  have h27 : Entails.eval a c214 := h 213 (by decide)
  have h28 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1760 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1759, some c1215, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1760 : lratChecker f1760 p1760 = .success := by decide +kernel
theorem unsat1760 : Unsatisfiable (PosFin 57) f1760 := by
  apply lratCheckerSound f1760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1760
  · intro a ha; simp [p1760] at ha; subst a; trivial
  · exact checked1760
theorem derived1760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1760 := by
  apply localUnsat_implies_entails f1760 [c1759, c1215] c1760 unsat1760 (by rfl) a
  have h0 : Entails.eval a c1759 := derived1759 a h
  have h1 : Entails.eval a c1215 := derived1215 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1761 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1489, some c1721, some c1759, some c1755, some c1752, some c1621, some c1751, some c385, some c392, some c1757, some c73, some c94, some c1219, some c1222, some c119, some c377, some c1136, some c266, some c225, some c354, some c352, some c68, some c108, some c111, some c45, some c84, some c297, some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1761 : lratChecker f1761 p1761 = .success := by decide +kernel
theorem unsat1761 : Unsatisfiable (PosFin 57) f1761 := by
  apply lratCheckerSound f1761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1761
  · intro a ha; simp [p1761] at ha; subst a; trivial
  · exact checked1761
theorem derived1761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1761 := by
  apply localUnsat_implies_entails f1761 [c1489, c1721, c1759, c1755, c1752, c1621, c1751, c385, c392, c1757, c73, c94, c1219, c1222, c119, c377, c1136, c266, c225, c354, c352, c68, c108, c111, c45, c84, c297] c1761 unsat1761 (by rfl) a
  have h0 : Entails.eval a c1489 := derived1489 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c1759 := derived1759 a h
  have h3 : Entails.eval a c1755 := derived1755 a h
  have h4 : Entails.eval a c1752 := derived1752 a h
  have h5 : Entails.eval a c1621 := derived1621 a h
  have h6 : Entails.eval a c1751 := derived1751 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c1757 := derived1757 a h
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c1222 := derived1222 a h
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c1136 := derived1136 a h
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c354 := h 353 (by decide)
  have h20 : Entails.eval a c352 := h 351 (by decide)
  have h21 : Entails.eval a c68 := h 67 (by decide)
  have h22 : Entails.eval a c108 := h 107 (by decide)
  have h23 : Entails.eval a c111 := h 110 (by decide)
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c84 := h 83 (by decide)
  have h26 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1762 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1761, some c1755, some c1224, some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p1762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1762 : lratChecker f1762 p1762 = .success := by decide +kernel
theorem unsat1762 : Unsatisfiable (PosFin 57) f1762 := by
  apply lratCheckerSound f1762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1762
  · intro a ha; simp [p1762] at ha; subst a; trivial
  · exact checked1762
theorem derived1762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1762 := by
  apply localUnsat_implies_entails f1762 [c1761, c1755, c1224] c1762 unsat1762 (by rfl) a
  have h0 : Entails.eval a c1761 := derived1761 a h
  have h1 : Entails.eval a c1755 := derived1755 a h
  have h2 : Entails.eval a c1224 := derived1224 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1763 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1761, some c1759, some c1221, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1763 : lratChecker f1763 p1763 = .success := by decide +kernel
theorem unsat1763 : Unsatisfiable (PosFin 57) f1763 := by
  apply lratCheckerSound f1763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1763
  · intro a ha; simp [p1763] at ha; subst a; trivial
  · exact checked1763
theorem derived1763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1763 := by
  apply localUnsat_implies_entails f1763 [c1761, c1759, c1221] c1763 unsat1763 (by rfl) a
  have h0 : Entails.eval a c1761 := derived1761 a h
  have h1 : Entails.eval a c1759 := derived1759 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1764 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1762, some c1721, some c377, some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p1764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1764 : lratChecker f1764 p1764 = .success := by decide +kernel
theorem unsat1764 : Unsatisfiable (PosFin 57) f1764 := by
  apply lratCheckerSound f1764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1764
  · intro a ha; simp [p1764] at ha; subst a; trivial
  · exact checked1764
theorem derived1764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1764 := by
  apply localUnsat_implies_entails f1764 [c1762, c1721, c377] c1764 unsat1764 (by rfl) a
  have h0 : Entails.eval a c1762 := derived1762 a h
  have h1 : Entails.eval a c1721 := derived1721 a h
  have h2 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1765 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1764, some c1489, some c73, some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1765 : lratChecker f1765 p1765 = .success := by decide +kernel
theorem unsat1765 : Unsatisfiable (PosFin 57) f1765 := by
  apply lratCheckerSound f1765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1765
  · intro a ha; simp [p1765] at ha; subst a; trivial
  · exact checked1765
theorem derived1765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1765 := by
  apply localUnsat_implies_entails f1765 [c1764, c1489, c73] c1765 unsat1765 (by rfl) a
  have h0 : Entails.eval a c1764 := derived1764 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1766 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1764, some c1489, some c53, some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1766 : lratChecker f1766 p1766 = .success := by decide +kernel
theorem unsat1766 : Unsatisfiable (PosFin 57) f1766 := by
  apply lratCheckerSound f1766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1766
  · intro a ha; simp [p1766] at ha; subst a; trivial
  · exact checked1766
theorem derived1766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1766 := by
  apply localUnsat_implies_entails f1766 [c1764, c1489, c53] c1766 unsat1766 (by rfl) a
  have h0 : Entails.eval a c1764 := derived1764 a h
  have h1 : Entails.eval a c1489 := derived1489 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1767 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1764, some c1621, some c1741, some c1721, some c997, some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p1767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1767 : lratChecker f1767 p1767 = .success := by decide +kernel
theorem unsat1767 : Unsatisfiable (PosFin 57) f1767 := by
  apply lratCheckerSound f1767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1767
  · intro a ha; simp [p1767] at ha; subst a; trivial
  · exact checked1767
theorem derived1767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1767 := by
  apply localUnsat_implies_entails f1767 [c1764, c1621, c1741, c1721, c997] c1767 unsat1767 (by rfl) a
  have h0 : Entails.eval a c1764 := derived1764 a h
  have h1 : Entails.eval a c1621 := derived1621 a h
  have h2 : Entails.eval a c1741 := derived1741 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c997 := derived997 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1768 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1766, some c1767, some c1765, some c342, some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1768 : lratChecker f1768 p1768 = .success := by decide +kernel
theorem unsat1768 : Unsatisfiable (PosFin 57) f1768 := by
  apply lratCheckerSound f1768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1768
  · intro a ha; simp [p1768] at ha; subst a; trivial
  · exact checked1768
theorem derived1768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1768 := by
  apply localUnsat_implies_entails f1768 [c1766, c1767, c1765, c342] c1768 unsat1768 (by rfl) a
  have h0 : Entails.eval a c1766 := derived1766 a h
  have h1 : Entails.eval a c1767 := derived1767 a h
  have h2 : Entails.eval a c1765 := derived1765 a h
  have h3 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1769 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1766, some c1752, some c1765, some c343, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1769 : lratChecker f1769 p1769 = .success := by decide +kernel
theorem unsat1769 : Unsatisfiable (PosFin 57) f1769 := by
  apply lratCheckerSound f1769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1769
  · intro a ha; simp [p1769] at ha; subst a; trivial
  · exact checked1769
theorem derived1769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1769 := by
  apply localUnsat_implies_entails f1769 [c1766, c1752, c1765, c343] c1769 unsat1769 (by rfl) a
  have h0 : Entails.eval a c1766 := derived1766 a h
  have h1 : Entails.eval a c1752 := derived1752 a h
  have h2 : Entails.eval a c1765 := derived1765 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1770 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1766, some c1763, some c1741, some c277, some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1770 : lratChecker f1770 p1770 = .success := by decide +kernel
theorem unsat1770 : Unsatisfiable (PosFin 57) f1770 := by
  apply lratCheckerSound f1770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1770
  · intro a ha; simp [p1770] at ha; subst a; trivial
  · exact checked1770
theorem derived1770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1770 := by
  apply localUnsat_implies_entails f1770 [c1766, c1763, c1741, c277] c1770 unsat1770 (by rfl) a
  have h0 : Entails.eval a c1766 := derived1766 a h
  have h1 : Entails.eval a c1763 := derived1763 a h
  have h2 : Entails.eval a c1741 := derived1741 a h
  have h3 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1771 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1768, some c1751, some c1769, some c72, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1771 : lratChecker f1771 p1771 = .success := by decide +kernel
theorem unsat1771 : Unsatisfiable (PosFin 57) f1771 := by
  apply lratCheckerSound f1771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1771
  · intro a ha; simp [p1771] at ha; subst a; trivial
  · exact checked1771
theorem derived1771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1771 := by
  apply localUnsat_implies_entails f1771 [c1768, c1751, c1769, c72] c1771 unsat1771 (by rfl) a
  have h0 : Entails.eval a c1768 := derived1768 a h
  have h1 : Entails.eval a c1751 := derived1751 a h
  have h2 : Entails.eval a c1769 := derived1769 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1772 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1771, some c1760, some c1756, some c15, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1772 : lratChecker f1772 p1772 = .success := by decide +kernel
theorem unsat1772 : Unsatisfiable (PosFin 57) f1772 := by
  apply lratCheckerSound f1772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1772
  · intro a ha; simp [p1772] at ha; subst a; trivial
  · exact checked1772
theorem derived1772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1772 := by
  apply localUnsat_implies_entails f1772 [c1771, c1760, c1756, c15] c1772 unsat1772 (by rfl) a
  have h0 : Entails.eval a c1771 := derived1771 a h
  have h1 : Entails.eval a c1760 := derived1760 a h
  have h2 : Entails.eval a c1756 := derived1756 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1773 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1772, some c1769, some c1768, some c172, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1773 : lratChecker f1773 p1773 = .success := by decide +kernel
theorem unsat1773 : Unsatisfiable (PosFin 57) f1773 := by
  apply lratCheckerSound f1773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1773
  · intro a ha; simp [p1773] at ha; subst a; trivial
  · exact checked1773
theorem derived1773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1773 := by
  apply localUnsat_implies_entails f1773 [c1772, c1769, c1768, c172] c1773 unsat1773 (by rfl) a
  have h0 : Entails.eval a c1772 := derived1772 a h
  have h1 : Entails.eval a c1769 := derived1769 a h
  have h2 : Entails.eval a c1768 := derived1768 a h
  have h3 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1774 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1772, some c1770, some c1768, some c170, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1774 : lratChecker f1774 p1774 = .success := by decide +kernel
theorem unsat1774 : Unsatisfiable (PosFin 57) f1774 := by
  apply lratCheckerSound f1774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1774
  · intro a ha; simp [p1774] at ha; subst a; trivial
  · exact checked1774
theorem derived1774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1774 := by
  apply localUnsat_implies_entails f1774 [c1772, c1770, c1768, c170] c1774 unsat1774 (by rfl) a
  have h0 : Entails.eval a c1772 := derived1772 a h
  have h1 : Entails.eval a c1770 := derived1770 a h
  have h2 : Entails.eval a c1768 := derived1768 a h
  have h3 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1775 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1774, some c1773, some c1762, some c1721, some c186]
def p1775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1775 : lratChecker f1775 p1775 = .success := by decide +kernel
theorem unsat1775 : Unsatisfiable (PosFin 57) f1775 := by
  apply lratCheckerSound f1775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1775
  · intro a ha; simp [p1775] at ha; subst a; trivial
  · exact checked1775
theorem derived1775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1775 := by
  apply localUnsat_implies_entails f1775 [c1774, c1773, c1762, c1721, c186] c1775 unsat1775 (by rfl) a
  have h0 : Entails.eval a c1774 := derived1774 a h
  have h1 : Entails.eval a c1773 := derived1773 a h
  have h2 : Entails.eval a c1762 := derived1762 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1775

end CochromaticTwenty.Certificates.B16_6_2
