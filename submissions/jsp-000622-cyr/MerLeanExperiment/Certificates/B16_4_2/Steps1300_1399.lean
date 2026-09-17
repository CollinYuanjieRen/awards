import MerLeanExperiment.Certificates.B16_4_2.Steps1200_1299

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1684 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c231, some c233, some c67, some c40, some c638, some c1316, some c217, some c353, some c143, some c168, some c207, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1569, c231, c233, c67, c40, c638, c1316, c217, c353, c143, c168, c207] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c231 := h 230 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c638 := derived638 a h
  have h6 : Entails.eval a c1316 := derived1316 a h
  have h7 : Entails.eval a c217 := h 216 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1678, some c1077, some c1665, some c631, some c24, some c120, some c1682, some c108, some c8, some c1683, some c112, some c16, some c1684, some c357, some c22, some c42, some c210, some c141, some c45, some c250, some c1584, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c1569, c1678, c1077, c1665, c631, c24, c120, c1682, c108, c8, c1683, c112, c16, c1684, c357, c22, c42, c210, c141, c45, c250, c1584] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1678 := derived1678 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1665 := derived1665 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c1682 := derived1682 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c1683 := derived1683 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c1684 := derived1684 a h
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c141 := h 140 (by decide)
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c1584 := derived1584 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨21, by decide⟩, false), (⟨36, by decide⟩, true), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c525, some c703, some c115, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c525, c703, c115] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c525 := derived525 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c53, some c56, some c209, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1569, c53, c56, c209] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c980, some c1015, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c980, c1015] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c980 := derived980 a h
  have h1 : Entails.eval a c1015 := derived1015 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1689 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c16, some c167, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c11, c16, c167] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1678, some c1077, some c1665, some c631, some c1685, some c267, some c266, some c1303, some c22, some c112, some c357, some c34, some c1686, some c1507, some c1689, some c1638, some c1688, some c1687, some c108, some c67, some c353, some c897, some c1491, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c1569, c1678, c1077, c1665, c631, c1685, c267, c266, c1303, c22, c112, c357, c34, c1686, c1507, c1689, c1638, c1688, c1687, c108, c67, c353, c897, c1491] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1678 := derived1678 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1665 := derived1665 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1685 := derived1685 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1303 := derived1303 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c1686 := derived1686 a h
  have h14 : Entails.eval a c1507 := derived1507 a h
  have h15 : Entails.eval a c1689 := derived1689 a h
  have h16 : Entails.eval a c1638 := derived1638 a h
  have h17 : Entails.eval a c1688 := derived1688 a h
  have h18 : Entails.eval a c1687 := derived1687 a h
  have h19 : Entails.eval a c108 := h 107 (by decide)
  have h20 : Entails.eval a c67 := h 66 (by decide)
  have h21 : Entails.eval a c353 := h 352 (by decide)
  have h22 : Entails.eval a c897 := derived897 a h
  have h23 : Entails.eval a c1491 := derived1491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1690, some c24, some c120, some c15, some c1665, some c231, some c1282, some c1678, some c1077, some c631, some c357, some c582, some c118, some c146, some c786, some c210, some c271, some c268, some c1681, some c141, some c1497, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c1690, c24, c120, c15, c1665, c231, c1282, c1678, c1077, c631, c357, c582, c118, c146, c786, c210, c271, c268, c1681, c141, c1497] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c1690 := derived1690 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c1665 := derived1665 a h
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1678 := derived1678 a h
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c631 := derived631 a h
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c582 := derived582 a h
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c786 := derived786 a h
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c271 := h 270 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c1681 := derived1681 a h
  have h19 : Entails.eval a c141 := h 140 (by decide)
  have h20 : Entails.eval a c1497 := derived1497 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1690, some c1282, some c1678, some c1665, some c231, some c1691, some c1464, some c233, some c112, some c1681, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1690, c1282, c1678, c1665, c231, c1691, c1464, c233, c112, c1681] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1690 := derived1690 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1678 := derived1678 a h
  have h3 : Entails.eval a c1665 := derived1665 a h
  have h4 : Entails.eval a c231 := h 230 (by decide)
  have h5 : Entails.eval a c1691 := derived1691 a h
  have h6 : Entails.eval a c1464 := derived1464 a h
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1681 := derived1681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1693 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1690, some c1282, some c631, some c1692, some c267, some c29, some c23, some c1678, some c1665, some c1688, some c57, some c53, some c313, some c212, some c56, some c283, some c111, some c353, some c67, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1569, c1690, c1282, c631, c1692, c267, c29, c23, c1678, c1665, c1688, c57, c53, c313, c212, c56, c283, c111, c353, c67] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1690 := derived1690 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1692 := derived1692 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c1678 := derived1678 a h
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c1688 := derived1688 a h
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c313 := h 312 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c283 := h 282 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1694 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1692, some c266, some c267, some c1690, some c1282, some c1678, some c1077, some c1496, some c29, some c1693, some c357, some c118, some c15, some c148, some c212, some c216, some c53, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c1569, c631, c1692, c266, c267, c1690, c1282, c1678, c1077, c1496, c29, c1693, c357, c118, c15, c148, c212, c216, c53] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1692 := derived1692 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c1690 := derived1690 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1678 := derived1678 a h
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c1496 := derived1496 a h
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c1693 := derived1693 a h
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c216 := h 215 (by decide)
  have h18 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1678, some c1694, some c112, some c1692, some c1690, some c1665, some c1660, some c1507, some c1689, some c1661, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1678, c1694, c112, c1692, c1690, c1665, c1660, c1507, c1689, c1661] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1678 := derived1678 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1692 := derived1692 a h
  have h4 : Entails.eval a c1690 := derived1690 a h
  have h5 : Entails.eval a c1665 := derived1665 a h
  have h6 : Entails.eval a c1660 := derived1660 a h
  have h7 : Entails.eval a c1507 := derived1507 a h
  have h8 : Entails.eval a c1689 := derived1689 a h
  have h9 : Entails.eval a c1661 := derived1661 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1665, some c631, some c1678, some c1077, some c1690, some c1282, some c1692, some c267, some c266, some c1694, some c112, some c1695, some c357, some c612, some c118, some c236, some c1681, some c1507, some c1689, some c15, some c1154, some c148, some c133, some c1230, some c216, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1665, c631, c1678, c1077, c1690, c1282, c1692, c267, c266, c1694, c112, c1695, c357, c612, c118, c236, c1681, c1507, c1689, c15, c1154, c148, c133, c1230, c216] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1678 := derived1678 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1690 := derived1690 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1692 := derived1692 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c1694 := derived1694 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c1695 := derived1695 a h
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c612 := derived612 a h
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c236 := h 235 (by decide)
  have h16 : Entails.eval a c1681 := derived1681 a h
  have h17 : Entails.eval a c1507 := derived1507 a h
  have h18 : Entails.eval a c1689 := derived1689 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c1154 := derived1154 a h
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c133 := h 132 (by decide)
  have h23 : Entails.eval a c1230 := derived1230 a h
  have h24 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨16, by decide⟩, false), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, true), (⟨36, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c66, some c206, some c1163, some c790, some c204, some c116, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c1569, c66, c206, c1163, c790, c204, c116] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c1163 := derived1163 a h
  have h4 : Entails.eval a c790 := derived790 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨36, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1665, some c66, some c355, some c19, some c525, some c39, some c1479, some c1673, some c14, some c532, some c125, some c354, some c70, some c1282, some c1450, some c638, some c173, some c20, some c328, some c88, some c245, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c1569, c1696, c1665, c66, c355, c19, c525, c39, c1479, c1673, c14, c532, c125, c354, c70, c1282, c1450, c638, c173, c20, c328, c88, c245] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c525 := derived525 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c1479 := derived1479 a h
  have h9 : Entails.eval a c1673 := derived1673 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c532 := derived532 a h
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c1450 := derived1450 a h
  have h17 : Entails.eval a c638 := derived638 a h
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c20 := h 19 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c88 := h 87 (by decide)
  have h22 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨36, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1665, some c66, some c355, some c19, some c525, some c39, some c1673, some c1479, some c354, some c14, some c1580, some c117, some c139, some c1698, some c206, some c1697, some c118, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1569, c1696, c1665, c66, c355, c19, c525, c39, c1673, c1479, c354, c14, c1580, c117, c139, c1698, c206, c1697, c118] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c525 := derived525 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c1673 := derived1673 a h
  have h9 : Entails.eval a c1479 := derived1479 a h
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c1580 := derived1580 a h
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c1698 := derived1698 a h
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c1697 := derived1697 a h
  have h18 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c1696, some c66, some c354, some c70, some c1282, some c19, some c39, some c355, some c1673, some c1479, some c631, some c525, some c1699, some c1681, some c1484, some c20, some c116, some c16, some c13, some c1001, some c166, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c1569, c1665, c1696, c66, c354, c70, c1282, c19, c39, c355, c1673, c1479, c631, c525, c1699, c1681, c1484, c20, c116, c16, c13, c1001, c166] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c1673 := derived1673 a h
  have h11 : Entails.eval a c1479 := derived1479 a h
  have h12 : Entails.eval a c631 := derived631 a h
  have h13 : Entails.eval a c525 := derived525 a h
  have h14 : Entails.eval a c1699 := derived1699 a h
  have h15 : Entails.eval a c1681 := derived1681 a h
  have h16 : Entails.eval a c1484 := derived1484 a h
  have h17 : Entails.eval a c20 := h 19 (by decide)
  have h18 : Entails.eval a c116 := h 115 (by decide)
  have h19 : Entails.eval a c16 := h 15 (by decide)
  have h20 : Entails.eval a c13 := h 12 (by decide)
  have h21 : Entails.eval a c1001 := derived1001 a h
  have h22 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1479, some c1673, some c14, some c16, some c1580, some c128, some c272, some c218, some c92, some c418, some c159, some c213, some c1278, some c53, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1569, c1479, c1673, c14, c16, c1580, c128, c272, c218, c92, c418, c159, c213, c1278, c53] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1479 := derived1479 a h
  have h2 : Entails.eval a c1673 := derived1673 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1580 := derived1580 a h
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c418 := derived418 a h
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c1278 := derived1278 a h
  have h14 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c66, some c206, some c204, some c1163, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c1569, c66, c206, c204, c1163] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c1163 := derived1163 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1665, some c19, some c39, some c66, some c354, some c355, some c70, some c1282, some c1701, some c631, some c1479, some c1673, some c14, some c1641, some c1700, some c1450, some c139, some c125, some c532, some c332, some c175, some c1702, some c638, some c173, some c245, some c328, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1569, c1696, c1665, c19, c39, c66, c354, c355, c70, c1282, c1701, c631, c1479, c1673, c14, c1641, c1700, c1450, c139, c125, c532, c332, c175, c1702, c638, c173, c245, c328] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c1701 := derived1701 a h
  have h11 : Entails.eval a c631 := derived631 a h
  have h12 : Entails.eval a c1479 := derived1479 a h
  have h13 : Entails.eval a c1673 := derived1673 a h
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c1641 := derived1641 a h
  have h16 : Entails.eval a c1700 := derived1700 a h
  have h17 : Entails.eval a c1450 := derived1450 a h
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c532 := derived532 a h
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c1702 := derived1702 a h
  have h24 : Entails.eval a c638 := derived638 a h
  have h25 : Entails.eval a c173 := h 172 (by decide)
  have h26 : Entails.eval a c245 := h 244 (by decide)
  have h27 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c1696, some c66, some c354, some c70, some c1282, some c631, some c45, some c53, some c250, some c340, some c337, some c52, some c310, some c318, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c1569, c1665, c1696, c66, c354, c70, c1282, c631, c45, c53, c250, c340, c337, c52, c310, c318] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c340 := h 339 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true), (⟨33, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c344, some c340, some c93, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c1569, c344, c340, c93] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1665, some c66, some c354, some c70, some c1282, some c39, some c19, some c1450, some c1705, some c355, some c1673, some c1479, some c631, some c14, some c1701, some c1703, some c1641, some c52, some c272, some c218, some c1278, some c236, some c1704, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c1569, c1696, c1665, c66, c354, c70, c1282, c39, c19, c1450, c1705, c355, c1673, c1479, c631, c14, c1701, c1703, c1641, c52, c272, c218, c1278, c236, c1704] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c1450 := derived1450 a h
  have h10 : Entails.eval a c1705 := derived1705 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1673 := derived1673 a h
  have h13 : Entails.eval a c1479 := derived1479 a h
  have h14 : Entails.eval a c631 := derived631 a h
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c1701 := derived1701 a h
  have h17 : Entails.eval a c1703 := derived1703 a h
  have h18 : Entails.eval a c1641 := derived1641 a h
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c272 := h 271 (by decide)
  have h21 : Entails.eval a c218 := h 217 (by decide)
  have h22 : Entails.eval a c1278 := derived1278 a h
  have h23 : Entails.eval a c236 := h 235 (by decide)
  have h24 : Entails.eval a c1704 := derived1704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c39, some c19, some c1696, some c66, some c354, some c70, some c1282, some c1450, some c355, some c1673, some c1479, some c631, some c1700, some c1706, some c1681, some c1484, some c16, some c128, some c137, some c324, some c328, some c173, some c205, some c204, some c582, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c1569, c1665, c39, c19, c1696, c66, c354, c70, c1282, c1450, c355, c1673, c1479, c631, c1700, c1706, c1681, c1484, c16, c128, c137, c324, c328, c173, c205, c204, c582] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c1696 := derived1696 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1450 := derived1450 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c1673 := derived1673 a h
  have h12 : Entails.eval a c1479 := derived1479 a h
  have h13 : Entails.eval a c631 := derived631 a h
  have h14 : Entails.eval a c1700 := derived1700 a h
  have h15 : Entails.eval a c1706 := derived1706 a h
  have h16 : Entails.eval a c1681 := derived1681 a h
  have h17 : Entails.eval a c1484 := derived1484 a h
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c128 := h 127 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c328 := h 327 (by decide)
  have h23 : Entails.eval a c173 := h 172 (by decide)
  have h24 : Entails.eval a c205 := h 204 (by decide)
  have h25 : Entails.eval a c204 := h 203 (by decide)
  have h26 : Entails.eval a c582 := derived582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1665, some c631, some c66, some c354, some c355, some c1707, some c267, some c266, some c236, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c1569, c1696, c1665, c631, c66, c354, c355, c1707, c267, c266, c236] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c1707 := derived1707 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c72, some c67, some c355, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c1569, c72, c67, c355] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1708, some c1077, some c358, some c1665, some c53, some c55, some c317, some c316, some c278, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c1569, c1696, c1708, c1077, c358, c1665, c53, c55, c317, c316, c278] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1665 := derived1665 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c43, some c211, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c23, c43, c211] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1665, some c1696, some c631, some c1077, some c1463, some c1282, some c111, some c1710, some c1711, some c355, some c162, some c10, some c358, some c210, some c146, some c15, some c128, some c139, some c336, some c328, some c1540, some c241, some c32, some c269, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1708, c1665, c1696, c631, c1077, c1463, c1282, c111, c1710, c1711, c355, c162, c10, c358, c210, c146, c15, c128, c139, c336, c328, c1540, c241, c32, c269] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1463 := derived1463 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1710 := derived1710 a h
  have h9 : Entails.eval a c1711 := derived1711 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c336 := h 335 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c1540 := derived1540 a h
  have h22 : Entails.eval a c241 := h 240 (by decide)
  have h23 : Entails.eval a c32 := h 31 (by decide)
  have h24 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1713 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1665, some c1696, some c631, some c1077, some c1463, some c1282, some c111, some c1710, some c1711, some c355, some c162, some c10, some c358, some c1712, some c118, some c15, some c128, some c139, some c91, some c336, some c1540, some c248, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1713 : lratChecker f1713 p1713 = .success := by decide +kernel
theorem unsat1713 : Unsatisfiable (PosFin 57) f1713 := by
  apply lratCheckerSound f1713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1713
  · intro a ha; simp [p1713] at ha; subst a; trivial
  · exact checked1713
theorem derived1713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1713 := by
  apply localUnsat_implies_entails f1713 [c1708, c1665, c1696, c631, c1077, c1463, c1282, c111, c1710, c1711, c355, c162, c10, c358, c1712, c118, c15, c128, c139, c91, c336, c1540, c248] c1713 unsat1713 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1463 := derived1463 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1710 := derived1710 a h
  have h9 : Entails.eval a c1711 := derived1711 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c1712 := derived1712 a h
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c1540 := derived1540 a h
  have h22 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1714 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1077, some c1696, some c1463, some c1282, some c358, some c1665, some c631, some c111, some c1710, some c1713, some c1500, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c1708, c1077, c1696, c1463, c1282, c358, c1665, c631, c111, c1710, c1713, c1500] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1463 := derived1463 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c1665 := derived1665 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c1710 := derived1710 a h
  have h10 : Entails.eval a c1713 := derived1713 a h
  have h11 : Entails.eval a c1500 := derived1500 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1708, some c1077, some c1696, some c1463, some c1282, some c358, some c1665, some c631, some c23, some c43, some c1711, some c265, some c797, some c141, some c45, some c53, some c1710, some c28, some c337, some c980, some c49, some c9, some c320, some c151, some c278, some c317, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c1569, c1708, c1077, c1696, c1463, c1282, c358, c1665, c631, c23, c43, c1711, c265, c797, c141, c45, c53, c1710, c28, c337, c980, c49, c9, c320, c151, c278, c317] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1463 := derived1463 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c1665 := derived1665 a h
  have h8 : Entails.eval a c631 := derived631 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c1711 := derived1711 a h
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c797 := derived797 a h
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c53 := h 52 (by decide)
  have h17 : Entails.eval a c1710 := derived1710 a h
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c337 := h 336 (by decide)
  have h20 : Entails.eval a c980 := derived980 a h
  have h21 : Entails.eval a c49 := h 48 (by decide)
  have h22 : Entails.eval a c9 := h 8 (by decide)
  have h23 : Entails.eval a c320 := h 319 (by decide)
  have h24 : Entails.eval a c151 := h 150 (by decide)
  have h25 : Entails.eval a c278 := h 277 (by decide)
  have h26 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨33, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c162, some c1708, some c67, some c163, some c9, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c1569, c1665, c162, c1708, c67, c163, c9] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c1708 := derived1708 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1708, some c1077, some c1696, some c1463, some c1282, some c1714, some c28, some c1665, some c1715, some c355, some c162, some c37, some c358, some c631, some c210, some c269, some c146, some c1001, some c15, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c1569, c1708, c1077, c1696, c1463, c1282, c1714, c28, c1665, c1715, c355, c162, c37, c358, c631, c210, c269, c146, c1001, c15] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1463 := derived1463 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1714 := derived1714 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c1665 := derived1665 a h
  have h9 : Entails.eval a c1715 := derived1715 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c162 := h 161 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c631 := derived631 a h
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c1001 := derived1001 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1665, some c1696, some c1714, some c1715, some c355, some c162, some c1708, some c1077, some c1463, some c1282, some c358, some c1717, some c118, some c230, some c15, some c1681, some c1001, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c1665, c1696, c1714, c1715, c355, c162, c1708, c1077, c1463, c1282, c358, c1717, c118, c230, c15, c1681, c1001] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1714 := derived1714 a h
  have h3 : Entails.eval a c1715 := derived1715 a h
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c1708 := derived1708 a h
  have h7 : Entails.eval a c1077 := derived1077 a h
  have h8 : Entails.eval a c1463 := derived1463 a h
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c1717 := derived1717 a h
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c1681 := derived1681 a h
  have h16 : Entails.eval a c1001 := derived1001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1719 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1715, some c355, some c1716, some c1049, some c37, some c1708, some c1077, some c1463, some c1282, some c358, some c1665, some c631, some c1687, some c209, some c49, some c350, some c348, some c51, some c97, some c315, some c344, some c309, some c317, some c316, some c278, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1719 : lratChecker f1719 p1719 = .success := by decide +kernel
theorem unsat1719 : Unsatisfiable (PosFin 57) f1719 := by
  apply lratCheckerSound f1719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1719
  · intro a ha; simp [p1719] at ha; subst a; trivial
  · exact checked1719
theorem derived1719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1719 := by
  apply localUnsat_implies_entails f1719 [c1569, c1696, c1715, c355, c1716, c1049, c37, c1708, c1077, c1463, c1282, c358, c1665, c631, c1687, c209, c49, c350, c348, c51, c97, c315, c344, c309, c317, c316, c278] c1719 unsat1719 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1715 := derived1715 a h
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c1716 := derived1716 a h
  have h5 : Entails.eval a c1049 := derived1049 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1708 := derived1708 a h
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c1463 := derived1463 a h
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c1665 := derived1665 a h
  have h13 : Entails.eval a c631 := derived631 a h
  have h14 : Entails.eval a c1687 := derived1687 a h
  have h15 : Entails.eval a c209 := h 208 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c350 := h 349 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c51 := h 50 (by decide)
  have h20 : Entails.eval a c97 := h 96 (by decide)
  have h21 : Entails.eval a c315 := h 314 (by decide)
  have h22 : Entails.eval a c344 := h 343 (by decide)
  have h23 : Entails.eval a c309 := h 308 (by decide)
  have h24 : Entails.eval a c317 := h 316 (by decide)
  have h25 : Entails.eval a c316 := h 315 (by decide)
  have h26 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1720 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1714, some c1719, some c35, some c1718, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1720 : lratChecker f1720 p1720 = .success := by decide +kernel
theorem unsat1720 : Unsatisfiable (PosFin 57) f1720 := by
  apply lratCheckerSound f1720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1720
  · intro a ha; simp [p1720] at ha; subst a; trivial
  · exact checked1720
theorem derived1720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1720 := by
  apply localUnsat_implies_entails f1720 [c1714, c1719, c35, c1718] c1720 unsat1720 (by rfl) a
  have h0 : Entails.eval a c1714 := derived1714 a h
  have h1 : Entails.eval a c1719 := derived1719 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c1718 := derived1718 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1721 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1708, some c112, some c28, some c21, some c1696, some c1077, some c358, some c1665, some c141, some c45, some c53, some c1710, some c337, some c980, some c9, some c49, some c11, some c151, some c892, some c317, some c278, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1721 : lratChecker f1721 p1721 = .success := by decide +kernel
theorem unsat1721 : Unsatisfiable (PosFin 57) f1721 := by
  apply lratCheckerSound f1721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1721
  · intro a ha; simp [p1721] at ha; subst a; trivial
  · exact checked1721
theorem derived1721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1721 := by
  apply localUnsat_implies_entails f1721 [c1569, c1708, c112, c28, c21, c1696, c1077, c358, c1665, c141, c45, c53, c1710, c337, c980, c9, c49, c11, c151, c892, c317, c278] c1721 unsat1721 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c1696 := derived1696 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c1665 := derived1665 a h
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c1710 := derived1710 a h
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c980 := derived980 a h
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c892 := derived892 a h
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1722 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1665, some c1688, some c56, some c313, some c702, some c280, some c143, some c319, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1722 : lratChecker f1722 p1722 = .success := by decide +kernel
theorem unsat1722 : Unsatisfiable (PosFin 57) f1722 := by
  apply lratCheckerSound f1722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1722
  · intro a ha; simp [p1722] at ha; subst a; trivial
  · exact checked1722
theorem derived1722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1722 := by
  apply localUnsat_implies_entails f1722 [c1708, c1665, c1688, c56, c313, c702, c280, c143, c319] c1722 unsat1722 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1688 := derived1688 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c702 := derived702 a h
  have h6 : Entails.eval a c280 := h 279 (by decide)
  have h7 : Entails.eval a c143 := h 142 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1723 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1665, some c631, some c211, some c313, some c703, some c56, some c980, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1723 : lratChecker f1723 p1723 = .success := by decide +kernel
theorem unsat1723 : Unsatisfiable (PosFin 57) f1723 := by
  apply lratCheckerSound f1723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1723
  · intro a ha; simp [p1723] at ha; subst a; trivial
  · exact checked1723
theorem derived1723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1723 := by
  apply localUnsat_implies_entails f1723 [c1708, c1665, c631, c211, c313, c703, c56, c980] c1723 unsat1723 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c211 := h 210 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c703 := derived703 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c980 := derived980 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1724 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c112, some c1696, some c1077, some c358, some c1665, some c28, some c1721, some c1278, some c1722, some c1723, some c702, some c143, some c980, some c46, some c56, some c342, some c319, some c309, some c344, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1724 : lratChecker f1724 p1724 = .success := by decide +kernel
theorem unsat1724 : Unsatisfiable (PosFin 57) f1724 := by
  apply lratCheckerSound f1724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1724
  · intro a ha; simp [p1724] at ha; subst a; trivial
  · exact checked1724
theorem derived1724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1724 := by
  apply localUnsat_implies_entails f1724 [c1708, c112, c1696, c1077, c358, c1665, c28, c1721, c1278, c1722, c1723, c702, c143, c980, c46, c56, c342, c319, c309, c344] c1724 unsat1724 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1665 := derived1665 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c1721 := derived1721 a h
  have h8 : Entails.eval a c1278 := derived1278 a h
  have h9 : Entails.eval a c1722 := derived1722 a h
  have h10 : Entails.eval a c1723 := derived1723 a h
  have h11 : Entails.eval a c702 := derived702 a h
  have h12 : Entails.eval a c143 := h 142 (by decide)
  have h13 : Entails.eval a c980 := derived980 a h
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c319 := h 318 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1725 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1720, some c112, some c1696, some c1665, some c631, some c1724, some c265, some c1687, some c703, some c1620, some c980, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1725 : lratChecker f1725 p1725 = .success := by decide +kernel
theorem unsat1725 : Unsatisfiable (PosFin 57) f1725 := by
  apply lratCheckerSound f1725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1725
  · intro a ha; simp [p1725] at ha; subst a; trivial
  · exact checked1725
theorem derived1725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1725 := by
  apply localUnsat_implies_entails f1725 [c1708, c1720, c112, c1696, c1665, c631, c1724, c265, c1687, c703, c1620, c980] c1725 unsat1725 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1720 := derived1720 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1665 := derived1665 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c1724 := derived1724 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c1687 := derived1687 a h
  have h9 : Entails.eval a c703 := derived703 a h
  have h10 : Entails.eval a c1620 := derived1620 a h
  have h11 : Entails.eval a c980 := derived980 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1726 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1708, some c1077, some c358, some c631, some c22, some c42, some c210, some c141, some c45, some c1584, some c250, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1726 : lratChecker f1726 p1726 = .success := by decide +kernel
theorem unsat1726 : Unsatisfiable (PosFin 57) f1726 := by
  apply lratCheckerSound f1726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1726
  · intro a ha; simp [p1726] at ha; subst a; trivial
  · exact checked1726
theorem derived1726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1726 := by
  apply localUnsat_implies_entails f1726 [c1569, c1696, c1708, c1077, c358, c631, c22, c42, c210, c141, c45, c1584, c250] c1726 unsat1726 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c1584 := derived1584 a h
  have h12 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1727 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1665, some c1696, some c1708, some c1720, some c112, some c1726, some c1282, some c1725, some c355, some c162, some c1077, some c358, some c786, some c1001, some c15, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1727 : lratChecker f1727 p1727 = .success := by decide +kernel
theorem unsat1727 : Unsatisfiable (PosFin 57) f1727 := by
  apply lratCheckerSound f1727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1727
  · intro a ha; simp [p1727] at ha; subst a; trivial
  · exact checked1727
theorem derived1727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1727 := by
  apply localUnsat_implies_entails f1727 [c1665, c1696, c1708, c1720, c112, c1726, c1282, c1725, c355, c162, c1077, c358, c786, c1001, c15] c1727 unsat1727 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c1720 := derived1720 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1726 := derived1726 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1725 := derived1725 a h
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c1077 := derived1077 a h
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c786 := derived786 a h
  have h13 : Entails.eval a c1001 := derived1001 a h
  have h14 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1728 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1720, some c112, some c1726, some c1282, some c1696, some c1077, some c358, some c1665, some c28, some c1727, some c268, some c269, some c230, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1728 : lratChecker f1728 p1728 = .success := by decide +kernel
theorem unsat1728 : Unsatisfiable (PosFin 57) f1728 := by
  apply lratCheckerSound f1728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1728
  · intro a ha; simp [p1728] at ha; subst a; trivial
  · exact checked1728
theorem derived1728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1728 := by
  apply localUnsat_implies_entails f1728 [c1708, c1720, c112, c1726, c1282, c1696, c1077, c358, c1665, c28, c1727, c268, c269, c230] c1728 unsat1728 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1720 := derived1720 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1726 := derived1726 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1696 := derived1696 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c1665 := derived1665 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c1727 := derived1727 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1729 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1708, some c1720, some c112, some c1726, some c1282, some c1696, some c1077, some c358, some c1665, some c631, some c1725, some c355, some c162, some c1049, some c1716, some c11, some c1728, some c265, some c1034, some c127, some c49, some c87, some c336, some c348, some c249, some c128, some c243, some c95, some c15, some c1681, some c761, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1729 : lratChecker f1729 p1729 = .success := by decide +kernel
theorem unsat1729 : Unsatisfiable (PosFin 57) f1729 := by
  apply lratCheckerSound f1729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1729
  · intro a ha; simp [p1729] at ha; subst a; trivial
  · exact checked1729
theorem derived1729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1729 := by
  apply localUnsat_implies_entails f1729 [c1569, c1708, c1720, c112, c1726, c1282, c1696, c1077, c358, c1665, c631, c1725, c355, c162, c1049, c1716, c11, c1728, c265, c1034, c127, c49, c87, c336, c348, c249, c128, c243, c95, c15, c1681, c761] c1729 unsat1729 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1720 := derived1720 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1726 := derived1726 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1696 := derived1696 a h
  have h7 : Entails.eval a c1077 := derived1077 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c631 := derived631 a h
  have h11 : Entails.eval a c1725 := derived1725 a h
  have h12 : Entails.eval a c355 := h 354 (by decide)
  have h13 : Entails.eval a c162 := h 161 (by decide)
  have h14 : Entails.eval a c1049 := derived1049 a h
  have h15 : Entails.eval a c1716 := derived1716 a h
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c1728 := derived1728 a h
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c1034 := derived1034 a h
  have h20 : Entails.eval a c127 := h 126 (by decide)
  have h21 : Entails.eval a c49 := h 48 (by decide)
  have h22 : Entails.eval a c87 := h 86 (by decide)
  have h23 : Entails.eval a c336 := h 335 (by decide)
  have h24 : Entails.eval a c348 := h 347 (by decide)
  have h25 : Entails.eval a c249 := h 248 (by decide)
  have h26 : Entails.eval a c128 := h 127 (by decide)
  have h27 : Entails.eval a c243 := h 242 (by decide)
  have h28 : Entails.eval a c95 := h 94 (by decide)
  have h29 : Entails.eval a c15 := h 14 (by decide)
  have h30 : Entails.eval a c1681 := derived1681 a h
  have h31 : Entails.eval a c761 := derived761 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1730 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1696, some c1708, some c1077, some c358, some c1665, some c631, some c1720, some c112, some c1726, some c1282, some c1729, some c35, some c265, some c1687, some c1506, some c355, some c37, some c1716, some c1034, some c1485, some c63, some c278, some c318, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1730 : lratChecker f1730 p1730 = .success := by decide +kernel
theorem unsat1730 : Unsatisfiable (PosFin 57) f1730 := by
  apply lratCheckerSound f1730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1730
  · intro a ha; simp [p1730] at ha; subst a; trivial
  · exact checked1730
theorem derived1730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1730 := by
  apply localUnsat_implies_entails f1730 [c1569, c1696, c1708, c1077, c358, c1665, c631, c1720, c112, c1726, c1282, c1729, c35, c265, c1687, c1506, c355, c37, c1716, c1034, c1485, c63, c278, c318] c1730 unsat1730 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1665 := derived1665 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c1720 := derived1720 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c1726 := derived1726 a h
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c1729 := derived1729 a h
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c1687 := derived1687 a h
  have h15 : Entails.eval a c1506 := derived1506 a h
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c1716 := derived1716 a h
  have h19 : Entails.eval a c1034 := derived1034 a h
  have h20 : Entails.eval a c1485 := derived1485 a h
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c278 := h 277 (by decide)
  have h23 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1731 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1708, some c1077, some c358, some c631, some c1730, some c266, some c22, some c1282, some c1665, some c230, some c267, some c111, some c112, some c29, some c32, some c268, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1731 : lratChecker f1731 p1731 = .success := by decide +kernel
theorem unsat1731 : Unsatisfiable (PosFin 57) f1731 := by
  apply lratCheckerSound f1731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1731
  · intro a ha; simp [p1731] at ha; subst a; trivial
  · exact checked1731
theorem derived1731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1731 := by
  apply localUnsat_implies_entails f1731 [c1696, c1708, c1077, c358, c631, c1730, c266, c22, c1282, c1665, c230, c267, c111, c112, c29, c32, c268] c1731 unsat1731 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1730 := derived1730 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1732 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1708, some c1077, some c358, some c631, some c1730, some c266, some c22, some c1282, some c1665, some c230, some c1731, some c1681, some c1275, some c1491, some c267, some c236, some c355, some c162, some c32, some c1719, some c9, some c124, some c767, some c89, some c246, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1732 : lratChecker f1732 p1732 = .success := by decide +kernel
theorem unsat1732 : Unsatisfiable (PosFin 57) f1732 := by
  apply lratCheckerSound f1732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1732
  · intro a ha; simp [p1732] at ha; subst a; trivial
  · exact checked1732
theorem derived1732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1732 := by
  apply localUnsat_implies_entails f1732 [c1696, c1708, c1077, c358, c631, c1730, c266, c22, c1282, c1665, c230, c1731, c1681, c1275, c1491, c267, c236, c355, c162, c32, c1719, c9, c124, c767, c89, c246] c1732 unsat1732 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1730 := derived1730 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1665 := derived1665 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c1731 := derived1731 a h
  have h12 : Entails.eval a c1681 := derived1681 a h
  have h13 : Entails.eval a c1275 := derived1275 a h
  have h14 : Entails.eval a c1491 := derived1491 a h
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c236 := h 235 (by decide)
  have h17 : Entails.eval a c355 := h 354 (by decide)
  have h18 : Entails.eval a c162 := h 161 (by decide)
  have h19 : Entails.eval a c32 := h 31 (by decide)
  have h20 : Entails.eval a c1719 := derived1719 a h
  have h21 : Entails.eval a c9 := h 8 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c767 := derived767 a h
  have h24 : Entails.eval a c89 := h 88 (by decide)
  have h25 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1733 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1665, some c1696, some c1708, some c1077, some c358, some c1730, some c267, some c266, some c1275, some c22, some c118, some c236, some c230, some c212, some c1282, some c355, some c162, some c1731, some c1491, some c1681, some c1732, some c11, some c127, some c136, some c336, some c334, some c207, some c183, some c125, some c15, some c209, some c63, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1733 : lratChecker f1733 p1733 = .success := by decide +kernel
theorem unsat1733 : Unsatisfiable (PosFin 57) f1733 := by
  apply lratCheckerSound f1733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1733
  · intro a ha; simp [p1733] at ha; subst a; trivial
  · exact checked1733
theorem derived1733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1733 := by
  apply localUnsat_implies_entails f1733 [c631, c1665, c1696, c1708, c1077, c358, c1730, c267, c266, c1275, c22, c118, c236, c230, c212, c1282, c355, c162, c1731, c1491, c1681, c1732, c11, c127, c136, c336, c334, c207, c183, c125, c15, c209, c63] c1733 unsat1733 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1708 := derived1708 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c1730 := derived1730 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c1275 := derived1275 a h
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c1731 := derived1731 a h
  have h19 : Entails.eval a c1491 := derived1491 a h
  have h20 : Entails.eval a c1681 := derived1681 a h
  have h21 : Entails.eval a c1732 := derived1732 a h
  have h22 : Entails.eval a c11 := h 10 (by decide)
  have h23 : Entails.eval a c127 := h 126 (by decide)
  have h24 : Entails.eval a c136 := h 135 (by decide)
  have h25 : Entails.eval a c336 := h 335 (by decide)
  have h26 : Entails.eval a c334 := h 333 (by decide)
  have h27 : Entails.eval a c207 := h 206 (by decide)
  have h28 : Entails.eval a c183 := h 182 (by decide)
  have h29 : Entails.eval a c125 := h 124 (by decide)
  have h30 : Entails.eval a c15 := h 14 (by decide)
  have h31 : Entails.eval a c209 := h 208 (by decide)
  have h32 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1734 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c120, some c235, some c202, some c203, some c813, some c359, some c792, some c69, some c233, some c72, some c12, some c1454, some c125, some c138, some c330, some c269, some c123, some c132, some c204, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1734 : lratChecker f1734 p1734 = .success := by decide +kernel
theorem unsat1734 : Unsatisfiable (PosFin 57) f1734 := by
  apply lratCheckerSound f1734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1734
  · intro a ha; simp [p1734] at ha; subst a; trivial
  · exact checked1734
theorem derived1734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1734 := by
  apply localUnsat_implies_entails f1734 [c1733, c1569, c120, c235, c202, c203, c813, c359, c792, c69, c233, c72, c12, c1454, c125, c138, c330, c269, c123, c132, c204] c1734 unsat1734 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c792 := derived792 a h
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c1454 := derived1454 a h
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c330 := h 329 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c123 := h 122 (by decide)
  have h19 : Entails.eval a c132 := h 131 (by decide)
  have h20 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1735 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1734, some c1590, some c76, some c69, some c356, some c1472, some c72, some c26, some c1711, some c54, some c53, some c316, some c144, some c12, some c13, some c139, some c172, some c203, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1735 : lratChecker f1735 p1735 = .success := by decide +kernel
theorem unsat1735 : Unsatisfiable (PosFin 57) f1735 := by
  apply lratCheckerSound f1735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1735
  · intro a ha; simp [p1735] at ha; subst a; trivial
  · exact checked1735
theorem derived1735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1735 := by
  apply localUnsat_implies_entails f1735 [c1569, c1733, c1734, c1590, c76, c69, c356, c1472, c72, c26, c1711, c54, c53, c316, c144, c12, c13, c139, c172, c203] c1735 unsat1735 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1734 := derived1734 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c1472 := derived1472 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1711 := derived1711 a h
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c144 := h 143 (by decide)
  have h15 : Entails.eval a c12 := h 11 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c172 := h 171 (by decide)
  have h19 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1736 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1734, some c1590, some c1735, some c813, some c355, some c234, some c117, some c37, some c65, some c17, some c210, some c356, some c282, some c1414, some c313, some c269, some c1572, some c29, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1736 : lratChecker f1736 p1736 = .success := by decide +kernel
theorem unsat1736 : Unsatisfiable (PosFin 57) f1736 := by
  apply lratCheckerSound f1736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1736
  · intro a ha; simp [p1736] at ha; subst a; trivial
  · exact checked1736
theorem derived1736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1736 := by
  apply localUnsat_implies_entails f1736 [c1569, c1734, c1590, c1735, c813, c355, c234, c117, c37, c65, c17, c210, c356, c282, c1414, c313, c269, c1572, c29] c1736 unsat1736 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1734 := derived1734 a h
  have h2 : Entails.eval a c1590 := derived1590 a h
  have h3 : Entails.eval a c1735 := derived1735 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c1414 := derived1414 a h
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c1572 := derived1572 a h
  have h18 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1737 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1736, some c19, some c39, some c66, some c1479, some c353, some c355, some c235, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1737 : lratChecker f1737 p1737 = .success := by decide +kernel
theorem unsat1737 : Unsatisfiable (PosFin 57) f1737 := by
  apply lratCheckerSound f1737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1737
  · intro a ha; simp [p1737] at ha; subst a; trivial
  · exact checked1737
theorem derived1737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1737 := by
  apply localUnsat_implies_entails f1737 [c1569, c1736, c19, c39, c66, c1479, c353, c355, c235] c1737 unsat1737 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1736 := derived1736 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1479 := derived1479 a h
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1738 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c265, some c272, some c26, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1738 : lratChecker f1738 p1738 = .success := by decide +kernel
theorem unsat1738 : Unsatisfiable (PosFin 57) f1738 := by
  apply lratCheckerSound f1738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1738
  · intro a ha; simp [p1738] at ha; subst a; trivial
  · exact checked1738
theorem derived1738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1738 := by
  apply localUnsat_implies_entails f1738 [c1569, c265, c272, c26] c1738 unsat1738 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1739 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨18, by decide⟩, false), (⟨39, by decide⟩, false), (⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c120, some c202, some c203, some c140, some c127, some c269, some c331, some c233, some c136, some c356, some c1139, some c38, some c773, some c123, some c154, some c213, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1739 : lratChecker f1739 p1739 = .success := by decide +kernel
theorem unsat1739 : Unsatisfiable (PosFin 57) f1739 := by
  apply lratCheckerSound f1739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1739
  · intro a ha; simp [p1739] at ha; subst a; trivial
  · exact checked1739
theorem derived1739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1739 := by
  apply localUnsat_implies_entails f1739 [c1733, c120, c202, c203, c140, c127, c269, c331, c233, c136, c356, c1139, c38, c773, c123, c154, c213] c1739 unsat1739 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c1139 := derived1139 a h
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c773 := derived773 a h
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1740 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨18, by decide⟩, false), (⟨39, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1739, some c355, some c65, some c1034, some c356, some c145, some c1414, some c201, some c271, some c127, some c331, some c336, some c243, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1740 : lratChecker f1740 p1740 = .success := by decide +kernel
theorem unsat1740 : Unsatisfiable (PosFin 57) f1740 := by
  apply lratCheckerSound f1740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1740
  · intro a ha; simp [p1740] at ha; subst a; trivial
  · exact checked1740
theorem derived1740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1740 := by
  apply localUnsat_implies_entails f1740 [c1569, c1733, c1739, c355, c65, c1034, c356, c145, c1414, c201, c271, c127, c331, c336, c243] c1740 unsat1740 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1739 := derived1739 a h
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c1034 := derived1034 a h
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c331 := h 330 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1741 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1737, some c1738, some c23, some c29, some c813, some c1740, some c19, some c39, some c66, some c213, some c218, some c355, some c57, some c53, some c283, some c315, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1741 : lratChecker f1741 p1741 = .success := by decide +kernel
theorem unsat1741 : Unsatisfiable (PosFin 57) f1741 := by
  apply lratCheckerSound f1741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1741
  · intro a ha; simp [p1741] at ha; subst a; trivial
  · exact checked1741
theorem derived1741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1741 := by
  apply localUnsat_implies_entails f1741 [c1569, c1737, c1738, c23, c29, c813, c1740, c19, c39, c66, c213, c218, c355, c57, c53, c283, c315] c1741 unsat1741 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1737 := derived1737 a h
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c1740 := derived1740 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  have h12 : Entails.eval a c355 := h 354 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1742 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c24, some c120, some c235, some c202, some c203, some c8, some c359, some c792, some c233, some c72, some c12, some c138, some c132, some c269, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1742 : lratChecker f1742 p1742 = .success := by decide +kernel
theorem unsat1742 : Unsatisfiable (PosFin 57) f1742 := by
  apply lratCheckerSound f1742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1742
  · intro a ha; simp [p1742] at ha; subst a; trivial
  · exact checked1742
theorem derived1742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1742 := by
  apply localUnsat_implies_entails f1742 [c1733, c24, c120, c235, c202, c203, c8, c359, c792, c233, c72, c12, c138, c132, c269] c1742 unsat1742 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c792 := derived792 a h
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1743 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c76, some c1742, some c354, some c37, some c17, some c1711, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1743 : lratChecker f1743 p1743 = .success := by decide +kernel
theorem unsat1743 : Unsatisfiable (PosFin 57) f1743 := by
  apply lratCheckerSound f1743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1743
  · intro a ha; simp [p1743] at ha; subst a; trivial
  · exact checked1743
theorem derived1743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1743 := by
  apply localUnsat_implies_entails f1743 [c1569, c1282, c76, c1742, c354, c37, c17, c1711] c1743 unsat1743 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c1742 := derived1742 a h
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1744 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨38, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c358, some c269, some c210, some c1414, some c58, some c50, some c64, some c320, some c351, some c349, some c315, some c276, some c309, some c316, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1744 : lratChecker f1744 p1744 = .success := by decide +kernel
theorem unsat1744 : Unsatisfiable (PosFin 57) f1744 := by
  apply lratCheckerSound f1744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1744
  · intro a ha; simp [p1744] at ha; subst a; trivial
  · exact checked1744
theorem derived1744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1744 := by
  apply localUnsat_implies_entails f1744 [c358, c269, c210, c1414, c58, c50, c64, c320, c351, c349, c315, c276, c309, c316] c1744 unsat1744 (by rfl) a
  have h0 : Entails.eval a c358 := h 357 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c1414 := derived1414 a h
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c276 := h 275 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1745 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1572, some c211, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1745 : lratChecker f1745 p1745 = .success := by decide +kernel
theorem unsat1745 : Unsatisfiable (PosFin 57) f1745 := by
  apply lratCheckerSound f1745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1745
  · intro a ha; simp [p1745] at ha; subst a; trivial
  · exact checked1745
theorem derived1745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1745 := by
  apply localUnsat_implies_entails f1745 [c1572, c211] c1745 unsat1745 (by rfl) a
  have h0 : Entails.eval a c1572 := derived1572 a h
  have h1 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1746 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1741, some c1282, some c1743, some c813, some c235, some c117, some c355, some c201, some c971, some c37, some c1745, some c36, some c127, some c210, some c331, some c336, some c42, some c58, some c64, some c128, some c243, some c358, some c1360, some c1421, some c8, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1746 : lratChecker f1746 p1746 = .success := by decide +kernel
theorem unsat1746 : Unsatisfiable (PosFin 57) f1746 := by
  apply lratCheckerSound f1746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1746
  · intro a ha; simp [p1746] at ha; subst a; trivial
  · exact checked1746
theorem derived1746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1746 := by
  apply localUnsat_implies_entails f1746 [c1733, c1569, c1741, c1282, c1743, c813, c235, c117, c355, c201, c971, c37, c1745, c36, c127, c210, c331, c336, c42, c58, c64, c128, c243, c358, c1360, c1421, c8] c1746 unsat1746 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1741 := derived1741 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1743 := derived1743 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c971 := derived971 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c1745 := derived1745 a h
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c331 := h 330 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c42 := h 41 (by decide)
  have h19 : Entails.eval a c58 := h 57 (by decide)
  have h20 : Entails.eval a c64 := h 63 (by decide)
  have h21 : Entails.eval a c128 := h 127 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c358 := h 357 (by decide)
  have h24 : Entails.eval a c1360 := derived1360 a h
  have h25 : Entails.eval a c1421 := derived1421 a h
  have h26 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1747 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1746, some c19, some c39, some c66, some c1479, some c353, some c355, some c235, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1747 : lratChecker f1747 p1747 = .success := by decide +kernel
theorem unsat1747 : Unsatisfiable (PosFin 57) f1747 := by
  apply lratCheckerSound f1747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1747
  · intro a ha; simp [p1747] at ha; subst a; trivial
  · exact checked1747
theorem derived1747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1747 := by
  apply localUnsat_implies_entails f1747 [c1569, c1746, c19, c39, c66, c1479, c353, c355, c235] c1747 unsat1747 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1746 := derived1746 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c1479 := derived1479 a h
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1748 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨2, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1282, some c24, some c120, some c203, some c8, some c133, some c269, some c233, some c136, some c356, some c1139, some c1159, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1748 : lratChecker f1748 p1748 = .success := by decide +kernel
theorem unsat1748 : Unsatisfiable (PosFin 57) f1748 := by
  apply lratCheckerSound f1748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1748
  · intro a ha; simp [p1748] at ha; subst a; trivial
  · exact checked1748
theorem derived1748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1748 := by
  apply localUnsat_implies_entails f1748 [c1733, c1282, c24, c120, c203, c8, c133, c269, c233, c136, c356, c1139, c1159] c1748 unsat1748 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c1139 := derived1139 a h
  have h12 : Entails.eval a c1159 := derived1159 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1749 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1747, some c1738, some c23, some c813, some c1741, some c1282, some c36, some c355, some c37, some c17, some c1034, some c210, some c145, some c42, some c50, some c64, some c201, some c358, some c1744, some c351, some c315, some c127, some c114, some c52, some c336, some c8, some c128, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1749 : lratChecker f1749 p1749 = .success := by decide +kernel
theorem unsat1749 : Unsatisfiable (PosFin 57) f1749 := by
  apply lratCheckerSound f1749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1749
  · intro a ha; simp [p1749] at ha; subst a; trivial
  · exact checked1749
theorem derived1749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1749 := by
  apply localUnsat_implies_entails f1749 [c1569, c1733, c1747, c1738, c23, c813, c1741, c1282, c36, c355, c37, c17, c1034, c210, c145, c42, c50, c64, c201, c358, c1744, c351, c315, c127, c114, c52, c336, c8, c128] c1749 unsat1749 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1747 := derived1747 a h
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c1741 := derived1741 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c1034 := derived1034 a h
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c201 := h 200 (by decide)
  have h19 : Entails.eval a c358 := h 357 (by decide)
  have h20 : Entails.eval a c1744 := derived1744 a h
  have h21 : Entails.eval a c351 := h 350 (by decide)
  have h22 : Entails.eval a c315 := h 314 (by decide)
  have h23 : Entails.eval a c127 := h 126 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c52 := h 51 (by decide)
  have h26 : Entails.eval a c336 := h 335 (by decide)
  have h27 : Entails.eval a c8 := h 7 (by decide)
  have h28 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1750 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1741, some c1282, some c1747, some c1738, some c23, some c36, some c813, some c1749, some c24, some c120, some c1748, some c8, some c19, some c39, some c70, some c271, some c1360, some c233, some c357, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1750 : lratChecker f1750 p1750 = .success := by decide +kernel
theorem unsat1750 : Unsatisfiable (PosFin 57) f1750 := by
  apply lratCheckerSound f1750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1750
  · intro a ha; simp [p1750] at ha; subst a; trivial
  · exact checked1750
theorem derived1750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1750 := by
  apply localUnsat_implies_entails f1750 [c1569, c1741, c1282, c1747, c1738, c23, c36, c813, c1749, c24, c120, c1748, c8, c19, c39, c70, c271, c1360, c233, c357] c1750 unsat1750 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1741 := derived1741 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1747 := derived1747 a h
  have h4 : Entails.eval a c1738 := derived1738 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c1749 := derived1749 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c1748 := derived1748 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c271 := h 270 (by decide)
  have h17 : Entails.eval a c1360 := derived1360 a h
  have h18 : Entails.eval a c233 := h 232 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1751 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨39, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1479, some c39, some c69, some c1472, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1751 : lratChecker f1751 p1751 = .success := by decide +kernel
theorem unsat1751 : Unsatisfiable (PosFin 57) f1751 := by
  apply lratCheckerSound f1751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1751
  · intro a ha; simp [p1751] at ha; subst a; trivial
  · exact checked1751
theorem derived1751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1751 := by
  apply localUnsat_implies_entails f1751 [c1479, c39, c69, c1472] c1751 unsat1751 (by rfl) a
  have h0 : Entails.eval a c1479 := derived1479 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c1472 := derived1472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1752 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c23, some c43, some c267, some c224, some c26, some c17, some c1479, some c39, some c47, some c54, some c59, some c313, some c1751, some c1282, some c76, some c58, some c354, some c685, some c283, some c203, some c8, some c359, some c346, some c165, some c281, some c341, some c317, some c304, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1752 : lratChecker f1752 p1752 = .success := by decide +kernel
theorem unsat1752 : Unsatisfiable (PosFin 57) f1752 := by
  apply lratCheckerSound f1752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1752
  · intro a ha; simp [p1752] at ha; subst a; trivial
  · exact checked1752
theorem derived1752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1752 := by
  apply localUnsat_implies_entails f1752 [c1569, c1733, c23, c43, c267, c224, c26, c17, c1479, c39, c47, c54, c59, c313, c1751, c1282, c76, c58, c354, c685, c283, c203, c8, c359, c346, c165, c281, c341, c317, c304] c1752 unsat1752 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c224 := h 223 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1479 := derived1479 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c313 := h 312 (by decide)
  have h14 : Entails.eval a c1751 := derived1751 a h
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c685 := derived685 a h
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c203 := h 202 (by decide)
  have h22 : Entails.eval a c8 := h 7 (by decide)
  have h23 : Entails.eval a c359 := h 358 (by decide)
  have h24 : Entails.eval a c346 := h 345 (by decide)
  have h25 : Entails.eval a c165 := h 164 (by decide)
  have h26 : Entails.eval a c281 := h 280 (by decide)
  have h27 : Entails.eval a c341 := h 340 (by decide)
  have h28 : Entails.eval a c317 := h 316 (by decide)
  have h29 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1753 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false), (⟨37, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c201, some c26, some c25, some c270, some c268, some c1414, some c27, some c516, some c12, some c148, some c124, some c202, some c333, some c126, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1753 : lratChecker f1753 p1753 = .success := by decide +kernel
theorem unsat1753 : Unsatisfiable (PosFin 57) f1753 := by
  apply lratCheckerSound f1753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1753
  · intro a ha; simp [p1753] at ha; subst a; trivial
  · exact checked1753
theorem derived1753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1753 := by
  apply localUnsat_implies_entails f1753 [c1569, c1733, c201, c26, c25, c270, c268, c1414, c27, c516, c12, c148, c124, c202, c333, c126] c1753 unsat1753 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1414 := derived1414 a h
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c516 := derived516 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1754 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1092, some c1436, some c29, some c202, some c148, some c212, some c216, some c53, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1754 : lratChecker f1754 p1754 = .success := by decide +kernel
theorem unsat1754 : Unsatisfiable (PosFin 57) f1754 := by
  apply lratCheckerSound f1754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1754
  · intro a ha; simp [p1754] at ha; subst a; trivial
  · exact checked1754
theorem derived1754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1754 := by
  apply localUnsat_implies_entails f1754 [c1733, c1569, c1092, c1436, c29, c202, c148, c212, c216, c53] c1754 unsat1754 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1092 := derived1092 a h
  have h3 : Entails.eval a c1436 := derived1436 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1755 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1750, some c1752, some c813, some c117, some c201, some c1754, some c25, some c1753, some c270, some c234, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1755 : lratChecker f1755 p1755 = .success := by decide +kernel
theorem unsat1755 : Unsatisfiable (PosFin 57) f1755 := by
  apply lratCheckerSound f1755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1755
  · intro a ha; simp [p1755] at ha; subst a; trivial
  · exact checked1755
theorem derived1755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1755 := by
  apply localUnsat_implies_entails f1755 [c1733, c1569, c1750, c1752, c813, c117, c201, c1754, c25, c1753, c270, c234] c1755 unsat1755 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1750 := derived1750 a h
  have h3 : Entails.eval a c1752 := derived1752 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1754 := derived1754 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c1753 := derived1753 a h
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1756 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1750, some c1752, some c813, some c1755, some c1590, some c355, some c234, some c17, some c266, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1756 : lratChecker f1756 p1756 = .success := by decide +kernel
theorem unsat1756 : Unsatisfiable (PosFin 57) f1756 := by
  apply lratCheckerSound f1756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1756
  · intro a ha; simp [p1756] at ha; subst a; trivial
  · exact checked1756
theorem derived1756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1756 := by
  apply localUnsat_implies_entails f1756 [c1569, c1750, c1752, c813, c1755, c1590, c355, c234, c17, c266] c1756 unsat1756 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1750 := derived1750 a h
  have h2 : Entails.eval a c1752 := derived1752 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c1755 := derived1755 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c234 := h 233 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1757 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨36, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c219, some c217, some c64, some c281, some c223, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1757 : lratChecker f1757 p1757 = .success := by decide +kernel
theorem unsat1757 : Unsatisfiable (PosFin 57) f1757 := by
  apply lratCheckerSound f1757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1757
  · intro a ha; simp [p1757] at ha; subst a; trivial
  · exact checked1757
theorem derived1757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1757 := by
  apply localUnsat_implies_entails f1757 [c219, c217, c64, c281, c223] c1757 unsat1757 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1758 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨35, by decide⟩, false), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1750, some c1752, some c1756, some c1282, some c1303, some c17, some c355, some c26, some c813, some c117, some c270, some c228, some c356, some c1414, some c1757, some c58, some c223, some c221, some c281, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1758 : lratChecker f1758 p1758 = .success := by decide +kernel
theorem unsat1758 : Unsatisfiable (PosFin 57) f1758 := by
  apply lratCheckerSound f1758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1758
  · intro a ha; simp [p1758] at ha; subst a; trivial
  · exact checked1758
theorem derived1758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1758 := by
  apply localUnsat_implies_entails f1758 [c1569, c1750, c1752, c1756, c1282, c1303, c17, c355, c26, c813, c117, c270, c228, c356, c1414, c1757, c58, c223, c221, c281] c1758 unsat1758 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1750 := derived1750 a h
  have h2 : Entails.eval a c1752 := derived1752 a h
  have h3 : Entails.eval a c1756 := derived1756 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1303 := derived1303 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c1414 := derived1414 a h
  have h15 : Entails.eval a c1757 := derived1757 a h
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c223 := h 222 (by decide)
  have h18 : Entails.eval a c221 := h 220 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1759 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c347, some c339, some c94, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1759 : lratChecker f1759 p1759 = .success := by decide +kernel
theorem unsat1759 : Unsatisfiable (PosFin 57) f1759 := by
  apply lratCheckerSound f1759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1759
  · intro a ha; simp [p1759] at ha; subst a; trivial
  · exact checked1759
theorem derived1759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1759 := by
  apply localUnsat_implies_entails f1759 [c1569, c347, c339, c94] c1759 unsat1759 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1760 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨33, by decide⟩, false), (⟨6, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c51, some c104, some c338, some c45, some c315, some c313, some c283, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1760 : lratChecker f1760 p1760 = .success := by decide +kernel
theorem unsat1760 : Unsatisfiable (PosFin 57) f1760 := by
  apply lratCheckerSound f1760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1760
  · intro a ha; simp [p1760] at ha; subst a; trivial
  · exact checked1760
theorem derived1760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1760 := by
  apply localUnsat_implies_entails f1760 [c1569, c51, c104, c338, c45, c315, c313, c283] c1760 unsat1760 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1761 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1750, some c1752, some c1756, some c1282, some c1303, some c17, some c355, some c26, some c813, some c117, some c1760, some c339, some c1759, some c94, some c259, some c36, some c270, some c228, some c357, some c1423, some c1414, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1761 : lratChecker f1761 p1761 = .success := by decide +kernel
theorem unsat1761 : Unsatisfiable (PosFin 57) f1761 := by
  apply lratCheckerSound f1761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1761
  · intro a ha; simp [p1761] at ha; subst a; trivial
  · exact checked1761
theorem derived1761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1761 := by
  apply localUnsat_implies_entails f1761 [c1569, c1750, c1752, c1756, c1282, c1303, c17, c355, c26, c813, c117, c1760, c339, c1759, c94, c259, c36, c270, c228, c357, c1423, c1414] c1761 unsat1761 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1750 := derived1750 a h
  have h2 : Entails.eval a c1752 := derived1752 a h
  have h3 : Entails.eval a c1756 := derived1756 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1303 := derived1303 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c1760 := derived1760 a h
  have h12 : Entails.eval a c339 := h 338 (by decide)
  have h13 : Entails.eval a c1759 := derived1759 a h
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c259 := h 258 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  have h20 : Entails.eval a c1423 := derived1423 a h
  have h21 : Entails.eval a c1414 := derived1414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1762 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1750, some c1752, some c813, some c117, some c201, some c1756, some c1282, some c1303, some c17, some c355, some c1761, some c70, some c234, some c42, some c270, some c1758, some c223, some c899, some c133, some c44, some c8, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1762 : lratChecker f1762 p1762 = .success := by decide +kernel
theorem unsat1762 : Unsatisfiable (PosFin 57) f1762 := by
  apply lratCheckerSound f1762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1762
  · intro a ha; simp [p1762] at ha; subst a; trivial
  · exact checked1762
theorem derived1762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1762 := by
  apply localUnsat_implies_entails f1762 [c1733, c1569, c1750, c1752, c813, c117, c201, c1756, c1282, c1303, c17, c355, c1761, c70, c234, c42, c270, c1758, c223, c899, c133, c44, c8] c1762 unsat1762 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1750 := derived1750 a h
  have h3 : Entails.eval a c1752 := derived1752 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1756 := derived1756 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1303 := derived1303 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1761 := derived1761 a h
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c234 := h 233 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c1758 := derived1758 a h
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c899 := derived899 a h
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c44 := h 43 (by decide)
  have h22 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1763 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c201, some c203, some c171, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1763 : lratChecker f1763 p1763 = .success := by decide +kernel
theorem unsat1763 : Unsatisfiable (PosFin 57) f1763 := by
  apply lratCheckerSound f1763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1763
  · intro a ha; simp [p1763] at ha; subst a; trivial
  · exact checked1763
theorem derived1763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1763 := by
  apply localUnsat_implies_entails f1763 [c1733, c201, c203, c171] c1763 unsat1763 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1764 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨40, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1750, some c1752, some c813, some c1763, some c1762, some c1738, some c29, some c270, some c36, some c1754, some c140, some c26, some c521, some c271, some c13, some c136, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1764 : lratChecker f1764 p1764 = .success := by decide +kernel
theorem unsat1764 : Unsatisfiable (PosFin 57) f1764 := by
  apply lratCheckerSound f1764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1764
  · intro a ha; simp [p1764] at ha; subst a; trivial
  · exact checked1764
theorem derived1764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1764 := by
  apply localUnsat_implies_entails f1764 [c1569, c1750, c1752, c813, c1763, c1762, c1738, c29, c270, c36, c1754, c140, c26, c521, c271, c13, c136] c1764 unsat1764 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1750 := derived1750 a h
  have h2 : Entails.eval a c1752 := derived1752 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c1763 := derived1763 a h
  have h5 : Entails.eval a c1762 := derived1762 a h
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c1754 := derived1754 a h
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c521 := derived521 a h
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1765 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1762, some c1738, some c1750, some c1752, some c813, some c1763, some c1764, some c1282, some c1303, some c36, some c26, some c521, some c270, some c271, some c133, some c136, some c6, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1765 : lratChecker f1765 p1765 = .success := by decide +kernel
theorem unsat1765 : Unsatisfiable (PosFin 57) f1765 := by
  apply lratCheckerSound f1765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1765
  · intro a ha; simp [p1765] at ha; subst a; trivial
  · exact checked1765
theorem derived1765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1765 := by
  apply localUnsat_implies_entails f1765 [c1569, c1762, c1738, c1750, c1752, c813, c1763, c1764, c1282, c1303, c36, c26, c521, c270, c271, c133, c136, c6] c1765 unsat1765 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1762 := derived1762 a h
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1750 := derived1750 a h
  have h4 : Entails.eval a c1752 := derived1752 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c1763 := derived1763 a h
  have h7 : Entails.eval a c1764 := derived1764 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1303 := derived1303 a h
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c521 := derived521 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1766 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1750, some c1752, some c813, some c1762, some c1738, some c1765, some c355, some c17, some c66, some c1034, some c266, some c1303, some c145, some c1282, some c201, some c1590, some c65, some c127, some c1436, some c282, some c356, some c336, some c331, some c202, some c1709, some c1414, some c12, some c271, some c144, some c181, some c242, some c297, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1766 : lratChecker f1766 p1766 = .success := by decide +kernel
theorem unsat1766 : Unsatisfiable (PosFin 57) f1766 := by
  apply lratCheckerSound f1766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1766
  · intro a ha; simp [p1766] at ha; subst a; trivial
  · exact checked1766
theorem derived1766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1766 := by
  apply localUnsat_implies_entails f1766 [c1733, c1569, c1750, c1752, c813, c1762, c1738, c1765, c355, c17, c66, c1034, c266, c1303, c145, c1282, c201, c1590, c65, c127, c1436, c282, c356, c336, c331, c202, c1709, c1414, c12, c271, c144, c181, c242, c297] c1766 unsat1766 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1750 := derived1750 a h
  have h3 : Entails.eval a c1752 := derived1752 a h
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c1762 := derived1762 a h
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c1765 := derived1765 a h
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c1034 := derived1034 a h
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c1303 := derived1303 a h
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c1590 := derived1590 a h
  have h18 : Entails.eval a c65 := h 64 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c1436 := derived1436 a h
  have h21 : Entails.eval a c282 := h 281 (by decide)
  have h22 : Entails.eval a c356 := h 355 (by decide)
  have h23 : Entails.eval a c336 := h 335 (by decide)
  have h24 : Entails.eval a c331 := h 330 (by decide)
  have h25 : Entails.eval a c202 := h 201 (by decide)
  have h26 : Entails.eval a c1709 := derived1709 a h
  have h27 : Entails.eval a c1414 := derived1414 a h
  have h28 : Entails.eval a c12 := h 11 (by decide)
  have h29 : Entails.eval a c271 := h 270 (by decide)
  have h30 : Entails.eval a c144 := h 143 (by decide)
  have h31 : Entails.eval a c181 := h 180 (by decide)
  have h32 : Entails.eval a c242 := h 241 (by decide)
  have h33 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1767 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c203, some c202, some c72, some c172, some c357, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1767 : lratChecker f1767 p1767 = .success := by decide +kernel
theorem unsat1767 : Unsatisfiable (PosFin 57) f1767 := by
  apply lratCheckerSound f1767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1767
  · intro a ha; simp [p1767] at ha; subst a; trivial
  · exact checked1767
theorem derived1767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1767 := by
  apply localUnsat_implies_entails f1767 [c1733, c203, c202, c72, c172, c357] c1767 unsat1767 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1768 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨14, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c37, some c17, some c67, some c357, some c118, some c146, some c210, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1768 : lratChecker f1768 p1768 = .success := by decide +kernel
theorem unsat1768 : Unsatisfiable (PosFin 57) f1768 := by
  apply lratCheckerSound f1768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1768
  · intro a ha; simp [p1768] at ha; subst a; trivial
  · exact checked1768
theorem derived1768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1768 := by
  apply localUnsat_implies_entails f1768 [c1569, c37, c17, c67, c357, c118, c146, c210] c1768 unsat1768 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1769 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c203, some c202, some c32, some c140, some c29, some c269, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1769 : lratChecker f1769 p1769 = .success := by decide +kernel
theorem unsat1769 : Unsatisfiable (PosFin 57) f1769 := by
  apply lratCheckerSound f1769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1769
  · intro a ha; simp [p1769] at ha; subst a; trivial
  · exact checked1769
theorem derived1769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1769 := by
  apply localUnsat_implies_entails f1769 [c1733, c203, c202, c32, c140, c29, c269] c1769 unsat1769 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1770 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1766, some c1077, some c111, some c120, some c1767, some c202, some c1768, some c353, some c235, some c1769, some c265, some c272, some c25, some c27, some c231, some c269, some c356, some c134, some c40, some c10, some c1302, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1770 : lratChecker f1770 p1770 = .success := by decide +kernel
theorem unsat1770 : Unsatisfiable (PosFin 57) f1770 := by
  apply lratCheckerSound f1770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1770
  · intro a ha; simp [p1770] at ha; subst a; trivial
  · exact checked1770
theorem derived1770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1770 := by
  apply localUnsat_implies_entails f1770 [c1733, c1569, c1766, c1077, c111, c120, c1767, c202, c1768, c353, c235, c1769, c265, c272, c25, c27, c231, c269, c356, c134, c40, c10, c1302] c1770 unsat1770 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1766 := derived1766 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c1767 := derived1767 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1768 := derived1768 a h
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c1769 := derived1769 a h
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c231 := h 230 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c40 := h 39 (by decide)
  have h21 : Entails.eval a c10 := h 9 (by decide)
  have h22 : Entails.eval a c1302 := derived1302 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1771 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1766, some c111, some c1077, some c24, some c120, some c202, some c203, some c1767, some c1768, some c353, some c1770, some c8, some c751, some c1092, some c32, some c140, some c133, some c269, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1771 : lratChecker f1771 p1771 = .success := by decide +kernel
theorem unsat1771 : Unsatisfiable (PosFin 57) f1771 := by
  apply lratCheckerSound f1771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1771
  · intro a ha; simp [p1771] at ha; subst a; trivial
  · exact checked1771
theorem derived1771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1771 := by
  apply localUnsat_implies_entails f1771 [c1733, c1569, c1766, c111, c1077, c24, c120, c202, c203, c1767, c1768, c353, c1770, c8, c751, c1092, c32, c140, c133, c269] c1771 unsat1771 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1766 := derived1766 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c1767 := derived1767 a h
  have h10 : Entails.eval a c1768 := derived1768 a h
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c1770 := derived1770 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c751 := derived751 a h
  have h15 : Entails.eval a c1092 := derived1092 a h
  have h16 : Entails.eval a c32 := h 31 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c133 := h 132 (by decide)
  have h19 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1772 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false), (⟨36, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1077, some c10, some c139, some c265, some c272, some c25, some c612, some c698, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1772 : lratChecker f1772 p1772 = .success := by decide +kernel
theorem unsat1772 : Unsatisfiable (PosFin 57) f1772 := by
  apply lratCheckerSound f1772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1772
  · intro a ha; simp [p1772] at ha; subst a; trivial
  · exact checked1772
theorem derived1772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1772 := by
  apply localUnsat_implies_entails f1772 [c1569, c1077, c10, c139, c265, c272, c25, c612, c698] c1772 unsat1772 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c612 := derived612 a h
  have h8 : Entails.eval a c698 := derived698 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1773 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1766, some c1077, some c111, some c1771, some c1709, some c356, some c358, some c23, some c1767, some c76, some c1282, some c1772, some c115, some c143, some c1479, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1773 : lratChecker f1773 p1773 = .success := by decide +kernel
theorem unsat1773 : Unsatisfiable (PosFin 57) f1773 := by
  apply lratCheckerSound f1773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1773
  · intro a ha; simp [p1773] at ha; subst a; trivial
  · exact checked1773
theorem derived1773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1773 := by
  apply localUnsat_implies_entails f1773 [c1766, c1077, c111, c1771, c1709, c356, c358, c23, c1767, c76, c1282, c1772, c115, c143, c1479] c1773 unsat1773 (by rfl) a
  have h0 : Entails.eval a c1766 := derived1766 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1771 := derived1771 a h
  have h4 : Entails.eval a c1709 := derived1709 a h
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c1767 := derived1767 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c1772 := derived1772 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c1479 := derived1479 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1774 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1766, some c1077, some c111, some c1771, some c1773, some c355, some c1768, some c202, some c17, some c37, some c1709, some c356, some c211, some c1772, some c57, some c60, some c143, some c316, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1774 : lratChecker f1774 p1774 = .success := by decide +kernel
theorem unsat1774 : Unsatisfiable (PosFin 57) f1774 := by
  apply lratCheckerSound f1774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1774
  · intro a ha; simp [p1774] at ha; subst a; trivial
  · exact checked1774
theorem derived1774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1774 := by
  apply localUnsat_implies_entails f1774 [c1569, c1733, c1766, c1077, c111, c1771, c1773, c355, c1768, c202, c17, c37, c1709, c356, c211, c1772, c57, c60, c143, c316] c1774 unsat1774 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1766 := derived1766 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1771 := derived1771 a h
  have h6 : Entails.eval a c1773 := derived1773 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c1768 := derived1768 a h
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c1709 := derived1709 a h
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c211 := h 210 (by decide)
  have h15 : Entails.eval a c1772 := derived1772 a h
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c143 := h 142 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1775 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1766, some c1077, some c111, some c1771, some c1709, some c356, some c358, some c1774, some c32, some c29, some c269, some c268, some c230, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1775 : lratChecker f1775 p1775 = .success := by decide +kernel
theorem unsat1775 : Unsatisfiable (PosFin 57) f1775 := by
  apply lratCheckerSound f1775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1775
  · intro a ha; simp [p1775] at ha; subst a; trivial
  · exact checked1775
theorem derived1775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1775 := by
  apply localUnsat_implies_entails f1775 [c1766, c1077, c111, c1771, c1709, c356, c358, c1774, c32, c29, c269, c268, c230] c1775 unsat1775 (by rfl) a
  have h0 : Entails.eval a c1766 := derived1766 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1771 := derived1771 a h
  have h4 : Entails.eval a c1709 := derived1709 a h
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c1774 := derived1774 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1776 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1766, some c1077, some c1771, some c358, some c1773, some c355, some c37, some c17, some c1775, some c1282, some c22, some c42, some c210, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1776 : lratChecker f1776 p1776 = .success := by decide +kernel
theorem unsat1776 : Unsatisfiable (PosFin 57) f1776 := by
  apply lratCheckerSound f1776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1776
  · intro a ha; simp [p1776] at ha; subst a; trivial
  · exact checked1776
theorem derived1776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1776 := by
  apply localUnsat_implies_entails f1776 [c1569, c1766, c1077, c1771, c358, c1773, c355, c37, c17, c1775, c1282, c22, c42, c210] c1776 unsat1776 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1766 := derived1766 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1771 := derived1771 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c1773 := derived1773 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c1775 := derived1775 a h
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1777 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c43, some c1767, some c685, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1777 : lratChecker f1777 p1777 = .success := by decide +kernel
theorem unsat1777 : Unsatisfiable (PosFin 57) f1777 := by
  apply lratCheckerSound f1777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1777
  · intro a ha; simp [p1777] at ha; subst a; trivial
  · exact checked1777
theorem derived1777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1777 := by
  apply localUnsat_implies_entails f1777 [c23, c43, c1767, c685] c1777 unsat1777 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c1767 := derived1767 a h
  have h3 : Entails.eval a c685 := derived685 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1778 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1766, some c1077, some c111, some c1777, some c1776, some c267, some c17, some c25, some c27, some c353, some c270, some c268, some c612, some c40, some c1302, some c214, some c10, some c57, some c134, some c685, some c202, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1778 : lratChecker f1778 p1778 = .success := by decide +kernel
theorem unsat1778 : Unsatisfiable (PosFin 57) f1778 := by
  apply lratCheckerSound f1778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1778
  · intro a ha; simp [p1778] at ha; subst a; trivial
  · exact checked1778
theorem derived1778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1778 := by
  apply localUnsat_implies_entails f1778 [c1569, c1733, c1766, c1077, c111, c1777, c1776, c267, c17, c25, c27, c353, c270, c268, c612, c40, c1302, c214, c10, c57, c134, c685, c202] c1778 unsat1778 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1766 := derived1766 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1777 := derived1777 a h
  have h6 : Entails.eval a c1776 := derived1776 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c612 := derived612 a h
  have h15 : Entails.eval a c40 := h 39 (by decide)
  have h16 : Entails.eval a c1302 := derived1302 a h
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c57 := h 56 (by decide)
  have h20 : Entails.eval a c134 := h 133 (by decide)
  have h21 : Entails.eval a c685 := derived685 a h
  have h22 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1779 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1776, some c1766, some c111, some c1778, some c29, some c1769, some c148, some c216, some c57, some c53, some c315, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1779 : lratChecker f1779 p1779 = .success := by decide +kernel
theorem unsat1779 : Unsatisfiable (PosFin 57) f1779 := by
  apply lratCheckerSound f1779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1779
  · intro a ha; simp [p1779] at ha; subst a; trivial
  · exact checked1779
theorem derived1779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1779 := by
  apply localUnsat_implies_entails f1779 [c1569, c1776, c1766, c111, c1778, c29, c1769, c148, c216, c57, c53, c315] c1779 unsat1779 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1776 := derived1776 a h
  have h2 : Entails.eval a c1766 := derived1766 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1778 := derived1778 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1769 := derived1769 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1780 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨36, by decide⟩, false), (⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c25, some c27, some c270, some c268, some c612, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1780 : lratChecker f1780 p1780 = .success := by decide +kernel
theorem unsat1780 : Unsatisfiable (PosFin 57) f1780 := by
  apply lratCheckerSound f1780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1780
  · intro a ha; simp [p1780] at ha; subst a; trivial
  · exact checked1780
theorem derived1780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1780 := by
  apply localUnsat_implies_entails f1780 [c1569, c25, c27, c270, c268, c612] c1780 unsat1780 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c612 := derived612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1781 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1776, some c1766, some c111, some c1077, some c1779, some c1709, some c1780, some c267, some c266, some c32, some c29, some c612, some c268, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1781 : lratChecker f1781 p1781 = .success := by decide +kernel
theorem unsat1781 : Unsatisfiable (PosFin 57) f1781 := by
  apply lratCheckerSound f1781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1781
  · intro a ha; simp [p1781] at ha; subst a; trivial
  · exact checked1781
theorem derived1781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1781 := by
  apply localUnsat_implies_entails f1781 [c1776, c1766, c111, c1077, c1779, c1709, c1780, c267, c266, c32, c29, c612, c268] c1781 unsat1781 (by rfl) a
  have h0 : Entails.eval a c1776 := derived1776 a h
  have h1 : Entails.eval a c1766 := derived1766 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c1709 := derived1709 a h
  have h6 : Entails.eval a c1780 := derived1780 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c612 := derived612 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1782 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c17, some c353, some c1077, some c202, some c751, some c5, some c8, some c582, some c73, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1782 : lratChecker f1782 p1782 = .success := by decide +kernel
theorem unsat1782 : Unsatisfiable (PosFin 57) f1782 := by
  apply lratCheckerSound f1782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1782
  · intro a ha; simp [p1782] at ha; subst a; trivial
  · exact checked1782
theorem derived1782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1782 := by
  apply localUnsat_implies_entails f1782 [c1733, c1569, c17, c353, c1077, c202, c751, c5, c8, c582, c73] c1782 unsat1782 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c582 := derived582 a h
  have h10 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1783 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c51, some c64, some c339, some c314, some c45, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1783 : lratChecker f1783 p1783 = .success := by decide +kernel
theorem unsat1783 : Unsatisfiable (PosFin 57) f1783 := by
  apply lratCheckerSound f1783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1783
  · intro a ha; simp [p1783] at ha; subst a; trivial
  · exact checked1783
theorem derived1783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1783 := by
  apply localUnsat_implies_entails f1783 [c1569, c51, c64, c339, c314, c45] c1783 unsat1783 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1783

end CochromaticTwenty.Certificates.B16_4_2
