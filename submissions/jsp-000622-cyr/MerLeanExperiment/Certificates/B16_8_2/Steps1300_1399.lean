import MerLeanExperiment.Certificates.B16_8_2.Steps1200_1299

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1681 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨38, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c1599, some c355, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c377, c1599, c355] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c1599 := derived1599 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1548, some c68, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1548, c68] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1548 := derived1548 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c12, some c159, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c1, c12, c159] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1684 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1680, some c367, some c1676, some c99, some c1671, some c70, some c78, some c1524, some c372, some c1125, some c1509, some c1681, some c89, some c1682, some c1683, some c166, some c153, some c373, some c149, some c355, some c1520, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1680, c367, c1676, c99, c1671, c70, c78, c1524, c372, c1125, c1509, c1681, c89, c1682, c1683, c166, c153, c373, c149, c355, c1520] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1680 := derived1680 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c1676 := derived1676 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c1524 := derived1524 a h
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c1125 := derived1125 a h
  have h10 : Entails.eval a c1509 := derived1509 a h
  have h11 : Entails.eval a c1681 := derived1681 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c1682 := derived1682 a h
  have h14 : Entails.eval a c1683 := derived1683 a h
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c373 := h 372 (by decide)
  have h18 : Entails.eval a c149 := h 148 (by decide)
  have h19 : Entails.eval a c355 := h 354 (by decide)
  have h20 : Entails.eval a c1520 := derived1520 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c295, some c1681, some c34, some c58, some c1509, some c333, some c67, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c295, c1681, c34, c58, c1509, c333, c67] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c1681 := derived1681 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c1509 := derived1509 a h
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1685, some c38, some c1125, some c46, some c335, some c67, some c293, some c34, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c1685, c38, c1125, c46, c335, c67, c293, c34] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c1685 := derived1685 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c1125 := derived1125 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1676, some c99, some c1671, some c367, some c1680, some c1684, some c370, some c66, some c1686, some c931, some c90, some c380, some c376, some c94, some c68, some c152, some c1683, some c178, some c1572, some c185, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1676, c99, c1671, c367, c1680, c1684, c370, c66, c1686, c931, c90, c380, c376, c94, c68, c152, c1683, c178, c1572, c185] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1676 := derived1676 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c1680 := derived1680 a h
  have h5 : Entails.eval a c1684 := derived1684 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c1686 := derived1686 a h
  have h9 : Entails.eval a c931 := derived931 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c152 := h 151 (by decide)
  have h16 : Entails.eval a c1683 := derived1683 a h
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c1572 := derived1572 a h
  have h19 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c335, some c333, some c58, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c335, c333, c58] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c335 := h 334 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1689 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1677, some c369, some c66, some c1672, some c67, some c1688, some c34, some c293, some c295, some c46, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c1677, c369, c66, c1672, c67, c1688, c34, c293, c295, c46] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c1677 := derived1677 a h
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1672 := derived1672 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c1688 := derived1688 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨10, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨50, by decide⟩, false), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c333, some c269, some c35, some c124, some c299, some c45, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c350, c333, c269, c35, c124, c299, c45] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1676, some c932, some c1687, some c1119, some c156, some c99, some c1677, some c369, some c66, some c1689, some c931, some c90, some c726, some c380, some c1632, some c285, some c363, some c325, some c365, some c1362, some c192, some c149, some c157, some c232, some c233, some c186, some c114, some c188, some c116, some c247, some c239, some c1690, some c57, some c331, some c339, some c210, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c1671, c1676, c932, c1687, c1119, c156, c99, c1677, c369, c66, c1689, c931, c90, c726, c380, c1632, c285, c363, c325, c365, c1362, c192, c149, c157, c232, c233, c186, c114, c188, c116, c247, c239, c1690, c57, c331, c339, c210] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1676 := derived1676 a h
  have h2 : Entails.eval a c932 := derived932 a h
  have h3 : Entails.eval a c1687 := derived1687 a h
  have h4 : Entails.eval a c1119 := derived1119 a h
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c1677 := derived1677 a h
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c1689 := derived1689 a h
  have h11 : Entails.eval a c931 := derived931 a h
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c726 := derived726 a h
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c1632 := derived1632 a h
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c365 := h 364 (by decide)
  have h20 : Entails.eval a c1362 := derived1362 a h
  have h21 : Entails.eval a c192 := h 191 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c157 := h 156 (by decide)
  have h24 : Entails.eval a c232 := h 231 (by decide)
  have h25 : Entails.eval a c233 := h 232 (by decide)
  have h26 : Entails.eval a c186 := h 185 (by decide)
  have h27 : Entails.eval a c114 := h 113 (by decide)
  have h28 : Entails.eval a c188 := h 187 (by decide)
  have h29 : Entails.eval a c116 := h 115 (by decide)
  have h30 : Entails.eval a c247 := h 246 (by decide)
  have h31 : Entails.eval a c239 := h 238 (by decide)
  have h32 : Entails.eval a c1690 := derived1690 a h
  have h33 : Entails.eval a c57 := h 56 (by decide)
  have h34 : Entails.eval a c331 := h 330 (by decide)
  have h35 : Entails.eval a c339 := h 338 (by decide)
  have h36 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1125, some c896, some c283, some c45, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1125, c896, c283, c45] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1693 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1692, some c35, some c323, some c317, some c57, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1692, c35, c323, c317, c57] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1692 := derived1692 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1694 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c89, some c1693, some c1313, some c363, some c365, some c1362, some c159, some c955, some c184, some c172, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c66, c89, c1693, c1313, c363, c365, c1362, c159, c955, c184, c172] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c1693 := derived1693 a h
  have h3 : Entails.eval a c1313 := derived1313 a h
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c1362 := derived1362 a h
  have h7 : Entails.eval a c159 := h 158 (by decide)
  have h8 : Entails.eval a c955 := derived955 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1676, some c99, some c932, some c1687, some c1119, some c1691, some c361, some c1694, some c377, some c376, some c90, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1671, c1676, c99, c932, c1687, c1119, c1691, c361, c1694, c377, c376, c90] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1676 := derived1676 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1687 := derived1687 a h
  have h5 : Entails.eval a c1119 := derived1119 a h
  have h6 : Entails.eval a c1691 := derived1691 a h
  have h7 : Entails.eval a c361 := h 360 (by decide)
  have h8 : Entails.eval a c1694 := derived1694 a h
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨30, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1251, some c1256, some c301, some c34, some c49, some c280, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1251, c1256, c301, c34, c49, c280] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1251 := derived1251 a h
  have h1 : Entails.eval a c1256 := derived1256 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c373, some c354, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c380, c373, c354] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c1623, some c66, some c89, some c368, some c1697, some c1085, some c1251, some c1280, some c1696, some c341, some c38, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c367, c1623, c66, c89, c368, c1697, c1085, c1251, c1280, c1696, c341, c38] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c1623 := derived1623 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c1697 := derived1697 a h
  have h6 : Entails.eval a c1085 := derived1085 a h
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c1280 := derived1280 a h
  have h9 : Entails.eval a c1696 := derived1696 a h
  have h10 : Entails.eval a c341 := h 340 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1623, some c1619, some c1698, some c1248, some c103, some c82, some c1454, some c295, some c45, some c44, some c286, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1623, c1619, c1698, c1248, c103, c82, c1454, c295, c45, c44, c286] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1623 := derived1623 a h
  have h1 : Entails.eval a c1619 := derived1619 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c1248 := derived1248 a h
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c1454 := derived1454 a h
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c378, some c89, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c841, c378, c89] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1623, some c1700, some c72, some c367, some c1619, some c1699, some c1357, some c103, some c82, some c95, some c372, some c1454, some c1697, some c89, some c1681, some c64, some c62, some c326, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1623, c1700, c72, c367, c1619, c1699, c1357, c103, c82, c95, c372, c1454, c1697, c89, c1681, c64, c62, c326] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1623 := derived1623 a h
  have h1 : Entails.eval a c1700 := derived1700 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c1619 := derived1619 a h
  have h5 : Entails.eval a c1699 := derived1699 a h
  have h6 : Entails.eval a c1357 := derived1357 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c1454 := derived1454 a h
  have h12 : Entails.eval a c1697 := derived1697 a h
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c1681 := derived1681 a h
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨51, by decide⟩, false), (⟨30, by decide⟩, false), (⟨4, by decide⟩, true), (⟨55, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c34, some c328, some c339, some c280, some c309, some c267, some c48, some c299, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c57, c34, c328, c339, c280, c309, c267, c48, c299] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨30, by decide⟩, false), (⟨4, by decide⟩, true), (⟨55, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1702, some c320, some c318, some c36, some c60, some c309, some c339, some c45, some c288, some c299, some c267, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1702, c320, c318, c36, c60, c309, c339, c45, c288, c299, c267] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1702 := derived1702 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c339 := h 338 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c238, some c17, some c114, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c238, c17, c114] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c238 := h 237 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c367, some c1671, some c89, some c66, some c368, some c1697, some c1085, some c88, some c1701, some c932, some c1703, some c151, some c354, some c10, some c290, some c172, some c179, some c186, some c1704, some c189, some c330, some c331, some c64, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c1695, c367, c1671, c89, c66, c368, c1697, c1085, c88, c1701, c932, c1703, c151, c354, c10, c290, c172, c179, c186, c1704, c189, c330, c331, c64] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c1697 := derived1697 a h
  have h7 : Entails.eval a c1085 := derived1085 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c1701 := derived1701 a h
  have h10 : Entails.eval a c932 := derived932 a h
  have h11 : Entails.eval a c1703 := derived1703 a h
  have h12 : Entails.eval a c151 := h 150 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c290 := h 289 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c1704 := derived1704 a h
  have h20 : Entails.eval a c189 := h 188 (by decide)
  have h21 : Entails.eval a c330 := h 329 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨51, by decide⟩, false), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c299, some c454, some c267, some c339, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c89, c299, c454, c267, c339] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c454 := derived454 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c350, some c57, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c328, c350, c57] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c1671, some c66, some c89, some c368, some c1697, some c88, some c1705, some c38, some c52, some c288, some c1707, some c454, some c1706, some c923, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c367, c1671, c66, c89, c368, c1697, c88, c1705, c38, c52, c288, c1707, c454, c1706, c923] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c1697 := derived1697 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c1705 := derived1705 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c1707 := derived1707 a h
  have h12 : Entails.eval a c454 := derived454 a h
  have h13 : Entails.eval a c1706 := derived1706 a h
  have h14 : Entails.eval a c923 := derived923 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c34, some c333, some c267, some c299, some c312, some c92, some c44, some c103, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c45, c34, c333, c267, c299, c312, c92, c44, c103] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨38, by decide⟩, true), (⟨31, by decide⟩, false), (⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c62, some c312, some c352, some c267, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c44, c62, c312, c352, c267] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c34, some c45, some c335, some c288, some c64, some c328, some c1709, some c1710, some c103, some c92, some c923, some c283, some c323, some c267, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c377, c34, c45, c335, c288, c64, c328, c1709, c1710, c103, c92, c923, c283, c323, c267] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c1709 := derived1709 a h
  have h8 : Entails.eval a c1710 := derived1710 a h
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c923 := derived923 a h
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c76, some c82, some c370, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1454, c76, c82, c370] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1713 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c339, some c293, some c267, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p1713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1713 : lratChecker f1713 p1713 = .success := by decide +kernel
theorem unsat1713 : Unsatisfiable (PosFin 57) f1713 := by
  apply lratCheckerSound f1713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1713
  · intro a ha; simp [p1713] at ha; subst a; trivial
  · exact checked1713
theorem derived1713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1713 := by
  apply localUnsat_implies_entails f1713 [c339, c293, c267] c1713 unsat1713 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1714 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c1671, some c1708, some c377, some c1711, some c295, some c38, some c52, some c335, some c1707, some c288, some c57, some c1712, some c103, some c92, some c1713, some c923, some c283, some c323, some c267, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c1695, c1671, c1708, c377, c1711, c295, c38, c52, c335, c1707, c288, c57, c1712, c103, c92, c1713, c923, c283, c323, c267] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1708 := derived1708 a h
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c1711 := derived1711 a h
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c335 := h 334 (by decide)
  have h9 : Entails.eval a c1707 := derived1707 a h
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c1712 := derived1712 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c1713 := derived1713 a h
  have h16 : Entails.eval a c923 := derived923 a h
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c330, some c331, some c64, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c330, c331, c64] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c330 := h 329 (by decide)
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1701, some c932, some c1714, some c1119, some c156, some c66, some c89, some c368, some c1313, some c88, some c363, some c365, some c1362, some c149, some c10, some c172, some c186, some c1704, some c1715, some c189, some c290, some c291, some c52, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c1671, c1695, c1701, c932, c1714, c1119, c156, c66, c89, c368, c1313, c88, c363, c365, c1362, c149, c10, c172, c186, c1704, c1715, c189, c290, c291, c52] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1714 := derived1714 a h
  have h5 : Entails.eval a c1119 := derived1119 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c368 := h 367 (by decide)
  have h10 : Entails.eval a c1313 := derived1313 a h
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c365 := h 364 (by decide)
  have h14 : Entails.eval a c1362 := derived1362 a h
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c1704 := derived1704 a h
  have h20 : Entails.eval a c1715 := derived1715 a h
  have h21 : Entails.eval a c189 := h 188 (by decide)
  have h22 : Entails.eval a c290 := h 289 (by decide)
  have h23 : Entails.eval a c291 := h 290 (by decide)
  have h24 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, true), (⟨31, by decide⟩, false), (⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c62, some c312, some c305, some c352, some c345, some c262, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c44, c62, c312, c305, c352, c345, c262] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c312 := h 311 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨16, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c299, some c921, some c191, some c148, some c140, some c241, some c247, some c109, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c333, c299, c921, c191, c148, c140, c241, c247, c109] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c140 := h 139 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1719 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1716, some c377, some c1671, some c1695, some c1701, some c932, some c1714, some c156, some c34, some c45, some c335, some c64, some c1717, some c103, some c92, some c1718, some c359, some c372, some c283, some c323, some c363, some c191, some c302, some c342, some c26, some c193, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1719 : lratChecker f1719 p1719 = .success := by decide +kernel
theorem unsat1719 : Unsatisfiable (PosFin 57) f1719 := by
  apply lratCheckerSound f1719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1719
  · intro a ha; simp [p1719] at ha; subst a; trivial
  · exact checked1719
theorem derived1719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1719 := by
  apply localUnsat_implies_entails f1719 [c1716, c377, c1671, c1695, c1701, c932, c1714, c156, c34, c45, c335, c64, c1717, c103, c92, c1718, c359, c372, c283, c323, c363, c191, c302, c342, c26, c193] c1719 unsat1719 (by rfl) a
  have h0 : Entails.eval a c1716 := derived1716 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1695 := derived1695 a h
  have h4 : Entails.eval a c1701 := derived1701 a h
  have h5 : Entails.eval a c932 := derived932 a h
  have h6 : Entails.eval a c1714 := derived1714 a h
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c1717 := derived1717 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c1718 := derived1718 a h
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c372 := h 371 (by decide)
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c323 := h 322 (by decide)
  have h20 : Entails.eval a c363 := h 362 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c302 := h 301 (by decide)
  have h23 : Entails.eval a c342 := h 341 (by decide)
  have h24 : Entails.eval a c26 := h 25 (by decide)
  have h25 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1720 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1454, some c76, some c82, some c369, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1720 : lratChecker f1720 p1720 = .success := by decide +kernel
theorem unsat1720 : Unsatisfiable (PosFin 57) f1720 := by
  apply lratCheckerSound f1720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1720
  · intro a ha; simp [p1720] at ha; subst a; trivial
  · exact checked1720
theorem derived1720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1720 := by
  apply localUnsat_implies_entails f1720 [c1454, c76, c82, c369] c1720 unsat1720 (by rfl) a
  have h0 : Entails.eval a c1454 := derived1454 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1721 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨4, by decide⟩, true), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1119, some c156, some c1325, some c921, some c339, some c363, some c347, some c365, some c1341, some c149, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1721 : lratChecker f1721 p1721 = .success := by decide +kernel
theorem unsat1721 : Unsatisfiable (PosFin 57) f1721 := by
  apply lratCheckerSound f1721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1721
  · intro a ha; simp [p1721] at ha; subst a; trivial
  · exact checked1721
theorem derived1721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1721 := by
  apply localUnsat_implies_entails f1721 [c1119, c156, c1325, c921, c339, c363, c347, c365, c1341, c149] c1721 unsat1721 (by rfl) a
  have h0 : Entails.eval a c1119 := derived1119 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c1325 := derived1325 a h
  have h3 : Entails.eval a c921 := derived921 a h
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c347 := h 346 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c1341 := derived1341 a h
  have h9 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1722 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1701, some c932, some c1714, some c1716, some c377, some c1719, some c295, some c38, some c52, some c335, some c57, some c1720, some c103, some c92, some c1721, some c359, some c372, some c283, some c323, some c363, some c191, some c302, some c342, some c26, some c193, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1722 : lratChecker f1722 p1722 = .success := by decide +kernel
theorem unsat1722 : Unsatisfiable (PosFin 57) f1722 := by
  apply lratCheckerSound f1722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1722
  · intro a ha; simp [p1722] at ha; subst a; trivial
  · exact checked1722
theorem derived1722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1722 := by
  apply localUnsat_implies_entails f1722 [c1671, c1695, c1701, c932, c1714, c1716, c377, c1719, c295, c38, c52, c335, c57, c1720, c103, c92, c1721, c359, c372, c283, c323, c363, c191, c302, c342, c26, c193] c1722 unsat1722 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1714 := derived1714 a h
  have h5 : Entails.eval a c1716 := derived1716 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c1719 := derived1719 a h
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c1720 := derived1720 a h
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c1721 := derived1721 a h
  have h17 : Entails.eval a c359 := h 358 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c363 := h 362 (by decide)
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c302 := h 301 (by decide)
  have h24 : Entails.eval a c342 := h 341 (by decide)
  have h25 : Entails.eval a c26 := h 25 (by decide)
  have h26 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1723 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨48, by decide⟩, false), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c103, some c68, some c301, some c48, some c36, some c288, some c341, some c64, some c328, some c1706, some c923, some c283, some c323, some c267, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1723 : lratChecker f1723 p1723 = .success := by decide +kernel
theorem unsat1723 : Unsatisfiable (PosFin 57) f1723 := by
  apply lratCheckerSound f1723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1723
  · intro a ha; simp [p1723] at ha; subst a; trivial
  · exact checked1723
theorem derived1723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1723 := by
  apply localUnsat_implies_entails f1723 [c89, c103, c68, c301, c48, c36, c288, c341, c64, c328, c1706, c923, c283, c323, c267] c1723 unsat1723 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c1706 := derived1706 a h
  have h11 : Entails.eval a c923 := derived923 a h
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1724 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c66, some c367, some c370, some c1723, some c88, some c82, some c1697, some c372, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1724 : lratChecker f1724 p1724 = .success := by decide +kernel
theorem unsat1724 : Unsatisfiable (PosFin 57) f1724 := by
  apply lratCheckerSound f1724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1724
  · intro a ha; simp [p1724] at ha; subst a; trivial
  · exact checked1724
theorem derived1724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1724 := by
  apply localUnsat_implies_entails f1724 [c89, c66, c367, c370, c1723, c88, c82, c1697, c372] c1724 unsat1724 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c1723 := derived1723 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c1697 := derived1697 a h
  have h8 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1725 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨28, by decide⟩, true), (⟨48, by decide⟩, true), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1701, some c932, some c1722, some c361, some c103, some c48, some c36, some c341, some c64, some c1721, some c359, some c372, some c283, some c323, some c363, some c191, some c302, some c340, some c26, some c193, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1725 : lratChecker f1725 p1725 = .success := by decide +kernel
theorem unsat1725 : Unsatisfiable (PosFin 57) f1725 := by
  apply lratCheckerSound f1725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1725
  · intro a ha; simp [p1725] at ha; subst a; trivial
  · exact checked1725
theorem derived1725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1725 := by
  apply localUnsat_implies_entails f1725 [c1671, c1695, c1701, c932, c1722, c361, c103, c48, c36, c341, c64, c1721, c359, c372, c283, c323, c363, c191, c302, c340, c26, c193] c1725 unsat1725 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1722 := derived1722 a h
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c1721 := derived1721 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  have h18 : Entails.eval a c302 := h 301 (by decide)
  have h19 : Entails.eval a c340 := h 339 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1726 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c89, some c66, some c1722, some c1695, some c1701, some c932, some c1724, some c1119, some c361, some c301, some c1725, some c88, some c597, some c1313, some c279, some c372, some c82, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1726 : lratChecker f1726 p1726 = .success := by decide +kernel
theorem unsat1726 : Unsatisfiable (PosFin 57) f1726 := by
  apply lratCheckerSound f1726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1726
  · intro a ha; simp [p1726] at ha; subst a; trivial
  · exact checked1726
theorem derived1726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1726 := by
  apply localUnsat_implies_entails f1726 [c1671, c89, c66, c1722, c1695, c1701, c932, c1724, c1119, c361, c301, c1725, c88, c597, c1313, c279, c372, c82] c1726 unsat1726 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c1722 := derived1722 a h
  have h4 : Entails.eval a c1695 := derived1695 a h
  have h5 : Entails.eval a c1701 := derived1701 a h
  have h6 : Entails.eval a c932 := derived932 a h
  have h7 : Entails.eval a c1724 := derived1724 a h
  have h8 : Entails.eval a c1119 := derived1119 a h
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c1725 := derived1725 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c597 := derived597 a h
  have h14 : Entails.eval a c1313 := derived1313 a h
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1727 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c38, some c89, some c1712, some c1707, some c288, some c454, some c1706, some c923, some c283, some c323, some c267, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1727 : lratChecker f1727 p1727 = .success := by decide +kernel
theorem unsat1727 : Unsatisfiable (PosFin 57) f1727 := by
  apply lratCheckerSound f1727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1727
  · intro a ha; simp [p1727] at ha; subst a; trivial
  · exact checked1727
theorem derived1727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1727 := by
  apply localUnsat_implies_entails f1727 [c52, c38, c89, c1712, c1707, c288, c454, c1706, c923, c283, c323, c267] c1727 unsat1727 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c1712 := derived1712 a h
  have h4 : Entails.eval a c1707 := derived1707 a h
  have h5 : Entails.eval a c288 := h 287 (by decide)
  have h6 : Entails.eval a c454 := derived454 a h
  have h7 : Entails.eval a c1706 := derived1706 a h
  have h8 : Entails.eval a c923 := derived923 a h
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c323 := h 322 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1728 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨36, by decide⟩, true), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c60, some c1721, some c359, some c372, some c283, some c323, some c363, some c191, some c302, some c342, some c26, some c193, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1728 : lratChecker f1728 p1728 = .success := by decide +kernel
theorem unsat1728 : Unsatisfiable (PosFin 57) f1728 := by
  apply lratCheckerSound f1728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1728
  · intro a ha; simp [p1728] at ha; subst a; trivial
  · exact checked1728
theorem derived1728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1728 := by
  apply localUnsat_implies_entails f1728 [c103, c60, c1721, c359, c372, c283, c323, c363, c191, c302, c342, c26, c193] c1728 unsat1728 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c1721 := derived1721 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1729 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1722, some c1671, some c1695, some c1701, some c932, some c89, some c1726, some c38, some c52, some c1727, some c361, some c341, some c1728, some c88, some c50, some c302, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1729 : lratChecker f1729 p1729 = .success := by decide +kernel
theorem unsat1729 : Unsatisfiable (PosFin 57) f1729 := by
  apply lratCheckerSound f1729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1729
  · intro a ha; simp [p1729] at ha; subst a; trivial
  · exact checked1729
theorem derived1729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1729 := by
  apply localUnsat_implies_entails f1729 [c1722, c1671, c1695, c1701, c932, c89, c1726, c38, c52, c1727, c361, c341, c1728, c88, c50, c302] c1729 unsat1729 (by rfl) a
  have h0 : Entails.eval a c1722 := derived1722 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c1701 := derived1701 a h
  have h4 : Entails.eval a c932 := derived932 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c1726 := derived1726 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c1727 := derived1727 a h
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c341 := h 340 (by decide)
  have h12 : Entails.eval a c1728 := derived1728 a h
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1730 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1701, some c932, some c1722, some c1729, some c377, some c68, some c361, some c103, some c1711, some c1712, some c295, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1730 : lratChecker f1730 p1730 = .success := by decide +kernel
theorem unsat1730 : Unsatisfiable (PosFin 57) f1730 := by
  apply lratCheckerSound f1730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1730
  · intro a ha; simp [p1730] at ha; subst a; trivial
  · exact checked1730
theorem derived1730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1730 := by
  apply localUnsat_implies_entails f1730 [c1671, c1695, c1701, c932, c1722, c1729, c377, c68, c361, c103, c1711, c1712, c295] c1730 unsat1730 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1722 := derived1722 a h
  have h5 : Entails.eval a c1729 := derived1729 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c1711 := derived1711 a h
  have h11 : Entails.eval a c1712 := derived1712 a h
  have h12 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1731 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1701, some c932, some c1730, some c70, some c369, some c370, some c361, some c931, some c34, some c45, some c319, some c64, some c1717, some c103, some c1728, some c1721, some c348, some c359, some c372, some c283, some c363, some c191, some c340, some c302, some c26, some c193, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1731 : lratChecker f1731 p1731 = .success := by decide +kernel
theorem unsat1731 : Unsatisfiable (PosFin 57) f1731 := by
  apply lratCheckerSound f1731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1731
  · intro a ha; simp [p1731] at ha; subst a; trivial
  · exact checked1731
theorem derived1731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1731 := by
  apply localUnsat_implies_entails f1731 [c1671, c1695, c1701, c932, c1730, c70, c369, c370, c361, c931, c34, c45, c319, c64, c1717, c103, c1728, c1721, c348, c359, c372, c283, c363, c191, c340, c302, c26, c193] c1731 unsat1731 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1730 := derived1730 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c361 := h 360 (by decide)
  have h9 : Entails.eval a c931 := derived931 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c1717 := derived1717 a h
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c1728 := derived1728 a h
  have h17 : Entails.eval a c1721 := derived1721 a h
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c359 := h 358 (by decide)
  have h20 : Entails.eval a c372 := h 371 (by decide)
  have h21 : Entails.eval a c283 := h 282 (by decide)
  have h22 : Entails.eval a c363 := h 362 (by decide)
  have h23 : Entails.eval a c191 := h 190 (by decide)
  have h24 : Entails.eval a c340 := h 339 (by decide)
  have h25 : Entails.eval a c302 := h 301 (by decide)
  have h26 : Entails.eval a c26 := h 25 (by decide)
  have h27 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1732 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨34, by decide⟩, true), (⟨31, by decide⟩, false), (⟨52, by decide⟩, false), (⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c57, some c103, some c1728, some c1721, some c359, some c372, some c283, some c323, some c363, some c191, some c340, some c26, some c225, some c212, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1732 : lratChecker f1732 p1732 = .success := by decide +kernel
theorem unsat1732 : Unsatisfiable (PosFin 57) f1732 := by
  apply lratCheckerSound f1732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1732
  · intro a ha; simp [p1732] at ha; subst a; trivial
  · exact checked1732
theorem derived1732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1732 := by
  apply localUnsat_implies_entails f1732 [c1671, c57, c103, c1728, c1721, c359, c372, c283, c323, c363, c191, c340, c26, c225, c212] c1732 unsat1732 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c1728 := derived1728 a h
  have h4 : Entails.eval a c1721 := derived1721 a h
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c323 := h 322 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c340 := h 339 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1733 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1730, some c70, some c1671, some c1695, some c1701, some c931, some c932, some c369, some c370, some c361, some c1731, some c279, some c38, some c52, some c319, some c1732, some c94, some c849, some c302, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1733 : lratChecker f1733 p1733 = .success := by decide +kernel
theorem unsat1733 : Unsatisfiable (PosFin 57) f1733 := by
  apply lratCheckerSound f1733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1733
  · intro a ha; simp [p1733] at ha; subst a; trivial
  · exact checked1733
theorem derived1733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1733 := by
  apply localUnsat_implies_entails f1733 [c1730, c70, c1671, c1695, c1701, c931, c932, c369, c370, c361, c1731, c279, c38, c52, c319, c1732, c94, c849, c302] c1733 unsat1733 (by rfl) a
  have h0 : Entails.eval a c1730 := derived1730 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1695 := derived1695 a h
  have h4 : Entails.eval a c1701 := derived1701 a h
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c932 := derived932 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c1731 := derived1731 a h
  have h11 : Entails.eval a c279 := h 278 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c319 := h 318 (by decide)
  have h15 : Entails.eval a c1732 := derived1732 a h
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c849 := derived849 a h
  have h18 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1734 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨31, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1129, some c283, some c267, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1734 : lratChecker f1734 p1734 = .success := by decide +kernel
theorem unsat1734 : Unsatisfiable (PosFin 57) f1734 := by
  apply lratCheckerSound f1734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1734
  · intro a ha; simp [p1734] at ha; subst a; trivial
  · exact checked1734
theorem derived1734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1734 := by
  apply localUnsat_implies_entails f1734 [c1129, c283, c267] c1734 unsat1734 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1735 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c1713, some c1709, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1735 : lratChecker f1735 p1735 = .success := by decide +kernel
theorem unsat1735 : Unsatisfiable (PosFin 57) f1735 := by
  apply lratCheckerSound f1735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1735
  · intro a ha; simp [p1735] at ha; subst a; trivial
  · exact checked1735
theorem derived1735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1735 := by
  apply localUnsat_implies_entails f1735 [c376, c1713, c1709] c1735 unsat1735 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c1713 := derived1713 a h
  have h2 : Entails.eval a c1709 := derived1709 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1736 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1461, some c1734, some c923, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1736 : lratChecker f1736 p1736 = .success := by decide +kernel
theorem unsat1736 : Unsatisfiable (PosFin 57) f1736 := by
  apply lratCheckerSound f1736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1736
  · intro a ha; simp [p1736] at ha; subst a; trivial
  · exact checked1736
theorem derived1736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1736 := by
  apply localUnsat_implies_entails f1736 [c1461, c1734, c923] c1736 unsat1736 (by rfl) a
  have h0 : Entails.eval a c1461 := derived1461 a h
  have h1 : Entails.eval a c1734 := derived1734 a h
  have h2 : Entails.eval a c923 := derived923 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1737 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c1671, some c1733, some c66, some c1730, some c70, some c1695, some c1701, some c931, some c1351, some c1735, some c1736, some c68, some c1170, some c923, some c283, some c323, some c267, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1737 : lratChecker f1737 p1737 = .success := by decide +kernel
theorem unsat1737 : Unsatisfiable (PosFin 57) f1737 := by
  apply lratCheckerSound f1737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1737
  · intro a ha; simp [p1737] at ha; subst a; trivial
  · exact checked1737
theorem derived1737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1737 := by
  apply localUnsat_implies_entails f1737 [c196, c1671, c1733, c66, c1730, c70, c1695, c1701, c931, c1351, c1735, c1736, c68, c1170, c923, c283, c323, c267] c1737 unsat1737 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1730 := derived1730 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1695 := derived1695 a h
  have h7 : Entails.eval a c1701 := derived1701 a h
  have h8 : Entails.eval a c931 := derived931 a h
  have h9 : Entails.eval a c1351 := derived1351 a h
  have h10 : Entails.eval a c1735 := derived1735 a h
  have h11 : Entails.eval a c1736 := derived1736 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c1170 := derived1170 a h
  have h14 : Entails.eval a c923 := derived923 a h
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c323 := h 322 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1738 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1730, some c70, some c1671, some c1695, some c1701, some c931, some c367, some c1582, some c287, some c196, some c236, some c1737, some c103, some c94, some c76, some c1697, some c372, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1738 : lratChecker f1738 p1738 = .success := by decide +kernel
theorem unsat1738 : Unsatisfiable (PosFin 57) f1738 := by
  apply lratCheckerSound f1738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1738
  · intro a ha; simp [p1738] at ha; subst a; trivial
  · exact checked1738
theorem derived1738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1738 := by
  apply localUnsat_implies_entails f1738 [c1733, c1730, c70, c1671, c1695, c1701, c931, c367, c1582, c287, c196, c236, c1737, c103, c94, c76, c1697, c372] c1738 unsat1738 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1730 := derived1730 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1695 := derived1695 a h
  have h5 : Entails.eval a c1701 := derived1701 a h
  have h6 : Entails.eval a c931 := derived931 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c1582 := derived1582 a h
  have h9 : Entails.eval a c287 := h 286 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c236 := h 235 (by decide)
  have h12 : Entails.eval a c1737 := derived1737 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c1697 := derived1697 a h
  have h17 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1739 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c103, some c1738, some c1730, some c70, some c1671, some c1701, some c931, some c932, some c285, some c1461, some c36, some c325, some c64, some c1721, some c359, some c372, some c1129, some c283, some c363, some c191, some c302, some c342, some c26, some c193, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1739 : lratChecker f1739 p1739 = .success := by decide +kernel
theorem unsat1739 : Unsatisfiable (PosFin 57) f1739 := by
  apply lratCheckerSound f1739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1739
  · intro a ha; simp [p1739] at ha; subst a; trivial
  · exact checked1739
theorem derived1739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1739 := by
  apply localUnsat_implies_entails f1739 [c1695, c103, c1738, c1730, c70, c1671, c1701, c931, c932, c285, c1461, c36, c325, c64, c1721, c359, c372, c1129, c283, c363, c191, c302, c342, c26, c193] c1739 unsat1739 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1730 := derived1730 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1701 := derived1701 a h
  have h7 : Entails.eval a c931 := derived931 a h
  have h8 : Entails.eval a c932 := derived932 a h
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c1461 := derived1461 a h
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c1721 := derived1721 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c1129 := derived1129 a h
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c363 := h 362 (by decide)
  have h20 : Entails.eval a c191 := h 190 (by decide)
  have h21 : Entails.eval a c302 := h 301 (by decide)
  have h22 : Entails.eval a c342 := h 341 (by decide)
  have h23 : Entails.eval a c26 := h 25 (by decide)
  have h24 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1740 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1671, some c1733, some c66, some c1695, some c1701, some c1730, some c931, some c932, some c103, some c1739, some c68, some c376, some c1170, some c359, some c1728, some c372, some c283, some c334, some c363, some c57, some c302, some c342, some c323, some c193, some c191, some c26, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1740 : lratChecker f1740 p1740 = .success := by decide +kernel
theorem unsat1740 : Unsatisfiable (PosFin 57) f1740 := by
  apply lratCheckerSound f1740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1740
  · intro a ha; simp [p1740] at ha; subst a; trivial
  · exact checked1740
theorem derived1740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1740 := by
  apply localUnsat_implies_entails f1740 [c1738, c1671, c1733, c66, c1695, c1701, c1730, c931, c932, c103, c1739, c68, c376, c1170, c359, c1728, c372, c283, c334, c363, c57, c302, c342, c323, c193, c191, c26] c1740 unsat1740 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c1695 := derived1695 a h
  have h5 : Entails.eval a c1701 := derived1701 a h
  have h6 : Entails.eval a c1730 := derived1730 a h
  have h7 : Entails.eval a c931 := derived931 a h
  have h8 : Entails.eval a c932 := derived932 a h
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c1739 := derived1739 a h
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c1170 := derived1170 a h
  have h14 : Entails.eval a c359 := h 358 (by decide)
  have h15 : Entails.eval a c1728 := derived1728 a h
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c334 := h 333 (by decide)
  have h19 : Entails.eval a c363 := h 362 (by decide)
  have h20 : Entails.eval a c57 := h 56 (by decide)
  have h21 : Entails.eval a c302 := h 301 (by decide)
  have h22 : Entails.eval a c342 := h 341 (by decide)
  have h23 : Entails.eval a c323 := h 322 (by decide)
  have h24 : Entails.eval a c193 := h 192 (by decide)
  have h25 : Entails.eval a c191 := h 190 (by decide)
  have h26 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1741 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1671, some c1695, some c1701, some c1730, some c931, some c932, some c1738, some c1119, some c1740, some c94, some c76, some c1313, some c372, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1741 : lratChecker f1741 p1741 = .success := by decide +kernel
theorem unsat1741 : Unsatisfiable (PosFin 57) f1741 := by
  apply lratCheckerSound f1741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1741
  · intro a ha; simp [p1741] at ha; subst a; trivial
  · exact checked1741
theorem derived1741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1741 := by
  apply localUnsat_implies_entails f1741 [c1733, c1671, c1695, c1701, c1730, c931, c932, c1738, c1119, c1740, c94, c76, c1313, c372] c1741 unsat1741 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c1701 := derived1701 a h
  have h4 : Entails.eval a c1730 := derived1730 a h
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c932 := derived932 a h
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1119 := derived1119 a h
  have h9 : Entails.eval a c1740 := derived1740 a h
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c1313 := derived1313 a h
  have h13 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1742 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c52, some c1730, some c70, some c1695, some c1671, some c1582, some c1712, some c288, some c196, some c103, some c1737, some c236, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1742 : lratChecker f1742 p1742 = .success := by decide +kernel
theorem unsat1742 : Unsatisfiable (PosFin 57) f1742 := by
  apply lratCheckerSound f1742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1742
  · intro a ha; simp [p1742] at ha; subst a; trivial
  · exact checked1742
theorem derived1742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1742 := by
  apply localUnsat_implies_entails f1742 [c1741, c52, c1730, c70, c1695, c1671, c1582, c1712, c288, c196, c103, c1737, c236] c1742 unsat1742 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c1730 := derived1730 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c1695 := derived1695 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1582 := derived1582 a h
  have h7 : Entails.eval a c1712 := derived1712 a h
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1737 := derived1737 a h
  have h12 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1743 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false), (⟨38, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c103, some c1728, some c325, some c349, some c68, some c57, some c376, some c359, some c372, some c283, some c323, some c363, some c191, some c302, some c340, some c26, some c193, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1743 : lratChecker f1743 p1743 = .success := by decide +kernel
theorem unsat1743 : Unsatisfiable (PosFin 57) f1743 := by
  apply lratCheckerSound f1743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1743
  · intro a ha; simp [p1743] at ha; subst a; trivial
  · exact checked1743
theorem derived1743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1743 := by
  apply localUnsat_implies_entails f1743 [c1671, c103, c1728, c325, c349, c68, c57, c376, c359, c372, c283, c323, c363, c191, c302, c340, c26, c193] c1743 unsat1743 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c1728 := derived1728 a h
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c302 := h 301 (by decide)
  have h15 : Entails.eval a c340 := h 339 (by decide)
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1744 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c1671, some c1701, some c932, some c1730, some c931, some c70, some c1733, some c66, some c1741, some c38, some c52, some c1742, some c1743, some c1454, some c76, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1744 : lratChecker f1744 p1744 = .success := by decide +kernel
theorem unsat1744 : Unsatisfiable (PosFin 57) f1744 := by
  apply lratCheckerSound f1744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1744
  · intro a ha; simp [p1744] at ha; subst a; trivial
  · exact checked1744
theorem derived1744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1744 := by
  apply localUnsat_implies_entails f1744 [c1695, c1671, c1701, c932, c1730, c931, c70, c1733, c66, c1741, c38, c52, c1742, c1743, c1454, c76] c1744 unsat1744 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c1701 := derived1701 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c1730 := derived1730 a h
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c1733 := derived1733 a h
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c1741 := derived1741 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c1742 := derived1742 a h
  have h13 : Entails.eval a c1743 := derived1743 a h
  have h14 : Entails.eval a c1454 := derived1454 a h
  have h15 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1745 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨39, by decide⟩, true), (⟨31, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c284, some c268, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1745 : lratChecker f1745 p1745 = .success := by decide +kernel
theorem unsat1745 : Unsatisfiable (PosFin 57) f1745 := by
  apply lratCheckerSound f1745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1745
  · intro a ha; simp [p1745] at ha; subst a; trivial
  · exact checked1745
theorem derived1745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1745 := by
  apply localUnsat_implies_entails f1745 [c324, c284, c268] c1745 unsat1745 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1746 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c338, some c298, some c762, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1746 : lratChecker f1746 p1746 = .success := by decide +kernel
theorem unsat1746 : Unsatisfiable (PosFin 57) f1746 := by
  apply lratCheckerSound f1746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1746
  · intro a ha; simp [p1746] at ha; subst a; trivial
  · exact checked1746
theorem derived1746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1746 := by
  apply localUnsat_implies_entails f1746 [c338, c298, c762] c1746 unsat1746 (by rfl) a
  have h0 : Entails.eval a c338 := h 337 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c762 := derived762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1747 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1744, some c99, some c1695, some c104, some c1671, some c66, some c88, some c370, some c1005, some c1004, some c82, some c372, some c286, some c326, some c195, some c1745, some c1465, some c1746, some c151, some c9, some c11, some c152, some c967, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1747 : lratChecker f1747 p1747 = .success := by decide +kernel
theorem unsat1747 : Unsatisfiable (PosFin 57) f1747 := by
  apply lratCheckerSound f1747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1747
  · intro a ha; simp [p1747] at ha; subst a; trivial
  · exact checked1747
theorem derived1747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1747 := by
  apply localUnsat_implies_entails f1747 [c1744, c99, c1695, c104, c1671, c66, c88, c370, c1005, c1004, c82, c372, c286, c326, c195, c1745, c1465, c1746, c151, c9, c11, c152, c967] c1747 unsat1747 (by rfl) a
  have h0 : Entails.eval a c1744 := derived1744 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c1005 := derived1005 a h
  have h9 : Entails.eval a c1004 := derived1004 a h
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c372 := h 371 (by decide)
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c326 := h 325 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c1745 := derived1745 a h
  have h16 : Entails.eval a c1465 := derived1465 a h
  have h17 : Entails.eval a c1746 := derived1746 a h
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c9 := h 8 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c967 := derived967 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1748 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨44, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1745, some c268, some c82, some c285, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1748 : lratChecker f1748 p1748 = .success := by decide +kernel
theorem unsat1748 : Unsatisfiable (PosFin 57) f1748 := by
  apply lratCheckerSound f1748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1748
  · intro a ha; simp [p1748] at ha; subst a; trivial
  · exact checked1748
theorem derived1748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1748 := by
  apply localUnsat_implies_entails f1748 [c1745, c268, c82, c285] c1748 unsat1748 (by rfl) a
  have h0 : Entails.eval a c1745 := derived1745 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1749 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c295, some c34, some c44, some c335, some c62, some c868, some c1748, some c328, some c326, some c40, some c82, some c287, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1749 : lratChecker f1749 p1749 = .success := by decide +kernel
theorem unsat1749 : Unsatisfiable (PosFin 57) f1749 := by
  apply lratCheckerSound f1749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1749
  · intro a ha; simp [p1749] at ha; subst a; trivial
  · exact checked1749
theorem derived1749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1749 := by
  apply localUnsat_implies_entails f1749 [c295, c34, c44, c335, c62, c868, c1748, c328, c326, c40, c82, c287] c1749 unsat1749 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c868 := derived868 a h
  have h6 : Entails.eval a c1748 := derived1748 a h
  have h7 : Entails.eval a c328 := h 327 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1750 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨31, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨50, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1749, some c70, some c370, some c287, some c1654, some c76, some c51, some c62, some c326, some c1745, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1750 : lratChecker f1750 p1750 = .success := by decide +kernel
theorem unsat1750 : Unsatisfiable (PosFin 57) f1750 := by
  apply lratCheckerSound f1750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1750
  · intro a ha; simp [p1750] at ha; subst a; trivial
  · exact checked1750
theorem derived1750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1750 := by
  apply localUnsat_implies_entails f1750 [c1749, c70, c370, c287, c1654, c76, c51, c62, c326, c1745] c1750 unsat1750 (by rfl) a
  have h0 : Entails.eval a c1749 := derived1749 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c1654 := derived1654 a h
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c1745 := derived1745 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1751 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c1744, some c104, some c99, some c1747, some c1671, some c1750, some c1414, some c378, some c377, some c1681, some c95, some c355, some c62, some c950, some c329, some c189, some c19, some c195, some c328, some c326, some c40, some c82, some c287, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1751 : lratChecker f1751 p1751 = .success := by decide +kernel
theorem unsat1751 : Unsatisfiable (PosFin 57) f1751 := by
  apply lratCheckerSound f1751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1751
  · intro a ha; simp [p1751] at ha; subst a; trivial
  · exact checked1751
theorem derived1751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1751 := by
  apply localUnsat_implies_entails f1751 [c1695, c1744, c104, c99, c1747, c1671, c1750, c1414, c378, c377, c1681, c95, c355, c62, c950, c329, c189, c19, c195, c328, c326, c40, c82, c287] c1751 unsat1751 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c1744 := derived1744 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1747 := derived1747 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1750 := derived1750 a h
  have h7 : Entails.eval a c1414 := derived1414 a h
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c1681 := derived1681 a h
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c355 := h 354 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c950 := derived950 a h
  have h15 : Entails.eval a c329 := h 328 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  have h19 : Entails.eval a c328 := h 327 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c40 := h 39 (by decide)
  have h22 : Entails.eval a c82 := h 81 (by decide)
  have h23 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1752 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1744, some c99, some c1695, some c104, some c1414, some c1671, some c1751, some c70, some c94, some c370, some c287, some c76, some c40, some c51, some c372, some c328, some c327, some c195, some c62, some c236, some c1746, some c404, some c354, some c311, some c329, some c289, some c769, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1752 : lratChecker f1752 p1752 = .success := by decide +kernel
theorem unsat1752 : Unsatisfiable (PosFin 57) f1752 := by
  apply lratCheckerSound f1752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1752
  · intro a ha; simp [p1752] at ha; subst a; trivial
  · exact checked1752
theorem derived1752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1752 := by
  apply localUnsat_implies_entails f1752 [c1744, c99, c1695, c104, c1414, c1671, c1751, c70, c94, c370, c287, c76, c40, c51, c372, c328, c327, c195, c62, c236, c1746, c404, c354, c311, c329, c289, c769] c1752 unsat1752 (by rfl) a
  have h0 : Entails.eval a c1744 := derived1744 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1414 := derived1414 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1751 := derived1751 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c195 := h 194 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c236 := h 235 (by decide)
  have h20 : Entails.eval a c1746 := derived1746 a h
  have h21 : Entails.eval a c404 := derived404 a h
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c329 := h 328 (by decide)
  have h25 : Entails.eval a c289 := h 288 (by decide)
  have h26 : Entails.eval a c769 := derived769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1753 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c82, some c370, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1753 : lratChecker f1753 p1753 = .success := by decide +kernel
theorem unsat1753 : Unsatisfiable (PosFin 57) f1753 := by
  apply lratCheckerSound f1753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1753
  · intro a ha; simp [p1753] at ha; subst a; trivial
  · exact checked1753
theorem derived1753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1753 := by
  apply localUnsat_implies_entails f1753 [c76, c82, c370] c1753 unsat1753 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1754 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c286, some c51, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1754 : lratChecker f1754 p1754 = .success := by decide +kernel
theorem unsat1754 : Unsatisfiable (PosFin 57) f1754 := by
  apply lratCheckerSound f1754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1754
  · intro a ha; simp [p1754] at ha; subst a; trivial
  · exact checked1754
theorem derived1754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1754 := by
  apply localUnsat_implies_entails f1754 [c288, c286, c51] c1754 unsat1754 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1755 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨29, by decide⟩, false), (⟨38, by decide⟩, false), (⟨31, by decide⟩, true), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨47, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c104, some c378, some c377, some c1248, some c335, some c95, some c56, some c326, some c195, some c1745, some c1746, some c152, some c151, some c9, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1755 : lratChecker f1755 p1755 = .success := by decide +kernel
theorem unsat1755 : Unsatisfiable (PosFin 57) f1755 := by
  apply lratCheckerSound f1755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1755
  · intro a ha; simp [p1755] at ha; subst a; trivial
  · exact checked1755
theorem derived1755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1755 := by
  apply localUnsat_implies_entails f1755 [c372, c104, c378, c377, c1248, c335, c95, c56, c326, c195, c1745, c1746, c152, c151, c9] c1755 unsat1755 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c1248 := derived1248 a h
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c1745 := derived1745 a h
  have h11 : Entails.eval a c1746 := derived1746 a h
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1756 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1744, some c99, some c1695, some c104, some c1414, some c1671, some c1747, some c1753, some c372, some c1754, some c1752, some c38, some c50, some c1755, some c70, some c94, some c327, some c63, some c326, some c195, some c19, some c1746, some c354, some c329, some c289, some c189, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1756 : lratChecker f1756 p1756 = .success := by decide +kernel
theorem unsat1756 : Unsatisfiable (PosFin 57) f1756 := by
  apply lratCheckerSound f1756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1756
  · intro a ha; simp [p1756] at ha; subst a; trivial
  · exact checked1756
theorem derived1756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1756 := by
  apply localUnsat_implies_entails f1756 [c1744, c99, c1695, c104, c1414, c1671, c1747, c1753, c372, c1754, c1752, c38, c50, c1755, c70, c94, c327, c63, c326, c195, c19, c1746, c354, c329, c289, c189] c1756 unsat1756 (by rfl) a
  have h0 : Entails.eval a c1744 := derived1744 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c1414 := derived1414 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1747 := derived1747 a h
  have h7 : Entails.eval a c1753 := derived1753 a h
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c1754 := derived1754 a h
  have h10 : Entails.eval a c1752 := derived1752 a h
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c1755 := derived1755 a h
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c195 := h 194 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c1746 := derived1746 a h
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c329 := h 328 (by decide)
  have h24 : Entails.eval a c289 := h 288 (by decide)
  have h25 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1757 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨45, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c372, some c1414, some c374, some c303, some c354, some c40, some c51, some c968, some c343, some c355, some c62, some c1745, some c326, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1757 : lratChecker f1757 p1757 = .success := by decide +kernel
theorem unsat1757 : Unsatisfiable (PosFin 57) f1757 := by
  apply lratCheckerSound f1757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1757
  · intro a ha; simp [p1757] at ha; subst a; trivial
  · exact checked1757
theorem derived1757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1757 := by
  apply localUnsat_implies_entails f1757 [c372, c1414, c374, c303, c354, c40, c51, c968, c343, c355, c62, c1745, c326] c1757 unsat1757 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c1414 := derived1414 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c968 := derived968 a h
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c1745 := derived1745 a h
  have h12 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1758 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c418, some c44, some c310, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1758 : lratChecker f1758 p1758 = .success := by decide +kernel
theorem unsat1758 : Unsatisfiable (PosFin 57) f1758 := by
  apply lratCheckerSound f1758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1758
  · intro a ha; simp [p1758] at ha; subst a; trivial
  · exact checked1758
theorem derived1758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1758 := by
  apply localUnsat_implies_entails f1758 [c1671, c418, c44, c310] c1758 unsat1758 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c418 := derived418 a h
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1759 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c63, some c56, some c350, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1759 : lratChecker f1759 p1759 = .success := by decide +kernel
theorem unsat1759 : Unsatisfiable (PosFin 57) f1759 := by
  apply lratCheckerSound f1759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1759
  · intro a ha; simp [p1759] at ha; subst a; trivial
  · exact checked1759
theorem derived1759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1759 := by
  apply localUnsat_implies_entails f1759 [c63, c56, c350] c1759 unsat1759 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1760 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1746, some c354, some c329, some c289, some c189, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1760 : lratChecker f1760 p1760 = .success := by decide +kernel
theorem unsat1760 : Unsatisfiable (PosFin 57) f1760 := by
  apply lratCheckerSound f1760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1760
  · intro a ha; simp [p1760] at ha; subst a; trivial
  · exact checked1760
theorem derived1760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1760 := by
  apply localUnsat_implies_entails f1760 [c1746, c354, c329, c289, c189] c1760 unsat1760 (by rfl) a
  have h0 : Entails.eval a c1746 := derived1746 a h
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1761 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c1759, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1761 : lratChecker f1761 p1761 = .success := by decide +kernel
theorem unsat1761 : Unsatisfiable (PosFin 57) f1761 := by
  apply lratCheckerSound f1761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1761
  · intro a ha; simp [p1761] at ha; subst a; trivial
  · exact checked1761
theorem derived1761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1761 := by
  apply localUnsat_implies_entails f1761 [c62, c1759] c1761 unsat1761 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c1759 := derived1759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1762 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1695, some c1744, some c104, some c99, some c1756, some c83, some c1671, some c1761, some c326, some c372, some c72, some c1414, some c1758, some c286, some c1757, some c195, some c94, some c19, some c1760, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1762 : lratChecker f1762 p1762 = .success := by decide +kernel
theorem unsat1762 : Unsatisfiable (PosFin 57) f1762 := by
  apply lratCheckerSound f1762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1762
  · intro a ha; simp [p1762] at ha; subst a; trivial
  · exact checked1762
theorem derived1762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1762 := by
  apply localUnsat_implies_entails f1762 [c1695, c1744, c104, c99, c1756, c83, c1671, c1761, c326, c372, c72, c1414, c1758, c286, c1757, c195, c94, c19, c1760] c1762 unsat1762 (by rfl) a
  have h0 : Entails.eval a c1695 := derived1695 a h
  have h1 : Entails.eval a c1744 := derived1744 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1756 := derived1756 a h
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c1761 := derived1761 a h
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c1414 := derived1414 a h
  have h12 : Entails.eval a c1758 := derived1758 a h
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c1757 := derived1757 a h
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c1760 := derived1760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1763 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1695, some c1744, some c104, some c99, some c1414, some c1756, some c72, some c83, some c372, some c1761, some c326, some c1762, some c50, some c286, some c195, some c19, some c1760, some c88, some c94, some c378, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1763 : lratChecker f1763 p1763 = .success := by decide +kernel
theorem unsat1763 : Unsatisfiable (PosFin 57) f1763 := by
  apply lratCheckerSound f1763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1763
  · intro a ha; simp [p1763] at ha; subst a; trivial
  · exact checked1763
theorem derived1763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1763 := by
  apply localUnsat_implies_entails f1763 [c1671, c1695, c1744, c104, c99, c1414, c1756, c72, c83, c372, c1761, c326, c1762, c50, c286, c195, c19, c1760, c88, c94, c378] c1763 unsat1763 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1744 := derived1744 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1414 := derived1414 a h
  have h6 : Entails.eval a c1756 := derived1756 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c1761 := derived1761 a h
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c1762 := derived1762 a h
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c1760 := derived1760 a h
  have h18 : Entails.eval a c88 := h 87 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1764 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c58, some c1632, some c317, some c67, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1764 : lratChecker f1764 p1764 = .success := by decide +kernel
theorem unsat1764 : Unsatisfiable (PosFin 57) f1764 := by
  apply lratCheckerSound f1764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1764
  · intro a ha; simp [p1764] at ha; subst a; trivial
  · exact checked1764
theorem derived1764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1764 := by
  apply localUnsat_implies_entails f1764 [c319, c58, c1632, c317, c67] c1764 unsat1764 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1765 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1764, some c34, some c279, some c46, some c52, some c299, some c277, some c67, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1765 : lratChecker f1765 p1765 = .success := by decide +kernel
theorem unsat1765 : Unsatisfiable (PosFin 57) f1765 := by
  apply lratCheckerSound f1765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1765
  · intro a ha; simp [p1765] at ha; subst a; trivial
  · exact checked1765
theorem derived1765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1765 := by
  apply localUnsat_implies_entails f1765 [c1764, c34, c279, c46, c52, c299, c277, c67] c1765 unsat1765 (by rfl) a
  have h0 : Entails.eval a c1764 := derived1764 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1766 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c45, some c319, some c64, some c1717, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1766 : lratChecker f1766 p1766 = .success := by decide +kernel
theorem unsat1766 : Unsatisfiable (PosFin 57) f1766 := by
  apply lratCheckerSound f1766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1766
  · intro a ha; simp [p1766] at ha; subst a; trivial
  · exact checked1766
theorem derived1766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1766 := by
  apply localUnsat_implies_entails f1766 [c34, c45, c319, c64, c1717] c1766 unsat1766 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c1717 := derived1717 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1767 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1763, some c1671, some c71, some c84, some c77, some c841, some c370, some c369, some c1117, some c80, some c361, some c1765, some c103, some c968, some c1118, some c359, some c9, some c164, some c159, some c1766, some c279, some c277, some c38, some c52, some c50, some c319, some c314, some c305, some c57, some c262, some c143, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1767 : lratChecker f1767 p1767 = .success := by decide +kernel
theorem unsat1767 : Unsatisfiable (PosFin 57) f1767 := by
  apply lratCheckerSound f1767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1767
  · intro a ha; simp [p1767] at ha; subst a; trivial
  · exact checked1767
theorem derived1767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1767 := by
  apply localUnsat_implies_entails f1767 [c1763, c1671, c71, c84, c77, c841, c370, c369, c1117, c80, c361, c1765, c103, c968, c1118, c359, c9, c164, c159, c1766, c279, c277, c38, c52, c50, c319, c314, c305, c57, c262, c143] c1767 unsat1767 (by rfl) a
  have h0 : Entails.eval a c1763 := derived1763 a h
  have h1 : Entails.eval a c1671 := derived1671 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c1117 := derived1117 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c1765 := derived1765 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c968 := derived968 a h
  have h14 : Entails.eval a c1118 := derived1118 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c1766 := derived1766 a h
  have h20 : Entails.eval a c279 := h 278 (by decide)
  have h21 : Entails.eval a c277 := h 276 (by decide)
  have h22 : Entails.eval a c38 := h 37 (by decide)
  have h23 : Entails.eval a c52 := h 51 (by decide)
  have h24 : Entails.eval a c50 := h 49 (by decide)
  have h25 : Entails.eval a c319 := h 318 (by decide)
  have h26 : Entails.eval a c314 := h 313 (by decide)
  have h27 : Entails.eval a c305 := h 304 (by decide)
  have h28 : Entails.eval a c57 := h 56 (by decide)
  have h29 : Entails.eval a c262 := h 261 (by decide)
  have h30 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1768 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1639, some c83, some c79, some c322, some c282, some c35, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1768 : lratChecker f1768 p1768 = .success := by decide +kernel
theorem unsat1768 : Unsatisfiable (PosFin 57) f1768 := by
  apply lratCheckerSound f1768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1768
  · intro a ha; simp [p1768] at ha; subst a; trivial
  · exact checked1768
theorem derived1768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1768 := by
  apply localUnsat_implies_entails f1768 [c1639, c83, c79, c322, c282, c35] c1768 unsat1768 (by rfl) a
  have h0 : Entails.eval a c1639 := derived1639 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1769 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨39, by decide⟩, false), (⟨44, by decide⟩, true), (⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c355, some c155, some c968, some c841, some c342, some c1041, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1769 : lratChecker f1769 p1769 = .success := by decide +kernel
theorem unsat1769 : Unsatisfiable (PosFin 57) f1769 := by
  apply lratCheckerSound f1769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1769
  · intro a ha; simp [p1769] at ha; subst a; trivial
  · exact checked1769
theorem derived1769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1769 := by
  apply localUnsat_implies_entails f1769 [c986, c355, c155, c968, c841, c342, c1041] c1769 unsat1769 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c155 := h 154 (by decide)
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c342 := h 341 (by decide)
  have h6 : Entails.eval a c1041 := derived1041 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1770 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1761, some c371, some c322, some c282, some c762, some c195, some c345, some c262, some c273, some c1769, some c290, some c289, some c94, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1770 : lratChecker f1770 p1770 = .success := by decide +kernel
theorem unsat1770 : Unsatisfiable (PosFin 57) f1770 := by
  apply lratCheckerSound f1770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1770
  · intro a ha; simp [p1770] at ha; subst a; trivial
  · exact checked1770
theorem derived1770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1770 := by
  apply localUnsat_implies_entails f1770 [c1761, c371, c322, c282, c762, c195, c345, c262, c273, c1769, c290, c289, c94] c1770 unsat1770 (by rfl) a
  have h0 : Entails.eval a c1761 := derived1761 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c322 := h 321 (by decide)
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c762 := derived762 a h
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c1769 := derived1769 a h
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1771 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨17, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c273, some c189, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1771 : lratChecker f1771 p1771 = .success := by decide +kernel
theorem unsat1771 : Unsatisfiable (PosFin 57) f1771 := by
  apply lratCheckerSound f1771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1771
  · intro a ha; simp [p1771] at ha; subst a; trivial
  · exact checked1771
theorem derived1771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1771 := by
  apply localUnsat_implies_entails f1771 [c313, c273, c189] c1771 unsat1771 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1772 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c88, some c95, some c378, some c94, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1772 : lratChecker f1772 p1772 = .success := by decide +kernel
theorem unsat1772 : Unsatisfiable (PosFin 57) f1772 := by
  apply lratCheckerSound f1772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1772
  · intro a ha; simp [p1772] at ha; subst a; trivial
  · exact checked1772
theorem derived1772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1772 := by
  apply localUnsat_implies_entails f1772 [c88, c95, c378, c94] c1772 unsat1772 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1773 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c83, some c1753, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1773 : lratChecker f1773 p1773 = .success := by decide +kernel
theorem unsat1773 : Unsatisfiable (PosFin 57) f1773 := by
  apply lratCheckerSound f1773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1773
  · intro a ha; simp [p1773] at ha; subst a; trivial
  · exact checked1773
theorem derived1773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1773 := by
  apply localUnsat_implies_entails f1773 [c83, c1753] c1773 unsat1773 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c1753 := derived1753 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1774 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨43, by decide⟩, true), (⟨29, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1767, some c97, some c99, some c1773, some c1772, some c1761, some c19, some c1771, some c1760, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1774 : lratChecker f1774 p1774 = .success := by decide +kernel
theorem unsat1774 : Unsatisfiable (PosFin 57) f1774 := by
  apply lratCheckerSound f1774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1774
  · intro a ha; simp [p1774] at ha; subst a; trivial
  · exact checked1774
theorem derived1774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1774 := by
  apply localUnsat_implies_entails f1774 [c1671, c1767, c97, c99, c1773, c1772, c1761, c19, c1771, c1760] c1774 unsat1774 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1767 := derived1767 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1773 := derived1773 a h
  have h5 : Entails.eval a c1772 := derived1772 a h
  have h6 : Entails.eval a c1761 := derived1761 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c1771 := derived1771 a h
  have h9 : Entails.eval a c1760 := derived1760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1775 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1763, some c1767, some c97, some c99, some c1671, some c1761, some c1758, some c1768, some c1773, some c1772, some c1770, some c1774, some c195, some c352, some c345, some c342, some c155, some c11, some c3, some c1118, some c158, some c298, some c273, some c262, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1775 : lratChecker f1775 p1775 = .success := by decide +kernel
theorem unsat1775 : Unsatisfiable (PosFin 57) f1775 := by
  apply lratCheckerSound f1775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1775
  · intro a ha; simp [p1775] at ha; subst a; trivial
  · exact checked1775
theorem derived1775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1775 := by
  apply localUnsat_implies_entails f1775 [c1763, c1767, c97, c99, c1671, c1761, c1758, c1768, c1773, c1772, c1770, c1774, c195, c352, c345, c342, c155, c11, c3, c1118, c158, c298, c273, c262] c1775 unsat1775 (by rfl) a
  have h0 : Entails.eval a c1763 := derived1763 a h
  have h1 : Entails.eval a c1767 := derived1767 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1761 := derived1761 a h
  have h6 : Entails.eval a c1758 := derived1758 a h
  have h7 : Entails.eval a c1768 := derived1768 a h
  have h8 : Entails.eval a c1773 := derived1773 a h
  have h9 : Entails.eval a c1772 := derived1772 a h
  have h10 : Entails.eval a c1770 := derived1770 a h
  have h11 : Entails.eval a c1774 := derived1774 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c345 := h 344 (by decide)
  have h15 : Entails.eval a c342 := h 341 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c3 := h 2 (by decide)
  have h19 : Entails.eval a c1118 := derived1118 a h
  have h20 : Entails.eval a c158 := h 157 (by decide)
  have h21 : Entails.eval a c298 := h 297 (by decide)
  have h22 : Entails.eval a c273 := h 272 (by decide)
  have h23 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1776 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1767, some c97, some c99, some c1773, some c1772, some c1761, some c1763, some c1758, some c1768, some c1775, some c302, some c312, some c305, some c155, some c11, some c3, some c1118, some c968, some c338, some c360, some c262, some c976, some c313, some c158, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1776 : lratChecker f1776 p1776 = .success := by decide +kernel
theorem unsat1776 : Unsatisfiable (PosFin 57) f1776 := by
  apply lratCheckerSound f1776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1776
  · intro a ha; simp [p1776] at ha; subst a; trivial
  · exact checked1776
theorem derived1776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1776 := by
  apply localUnsat_implies_entails f1776 [c1671, c1767, c97, c99, c1773, c1772, c1761, c1763, c1758, c1768, c1775, c302, c312, c305, c155, c11, c3, c1118, c968, c338, c360, c262, c976, c313, c158] c1776 unsat1776 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1767 := derived1767 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1773 := derived1773 a h
  have h5 : Entails.eval a c1772 := derived1772 a h
  have h6 : Entails.eval a c1761 := derived1761 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c1758 := derived1758 a h
  have h9 : Entails.eval a c1768 := derived1768 a h
  have h10 : Entails.eval a c1775 := derived1775 a h
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c312 := h 311 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c1118 := derived1118 a h
  have h18 : Entails.eval a c968 := derived968 a h
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c262 := h 261 (by decide)
  have h22 : Entails.eval a c976 := derived976 a h
  have h23 : Entails.eval a c313 := h 312 (by decide)
  have h24 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1777 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨47, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1761, some c1768, some c1773, some c1772, some c976, some c322, some c282, some c1465, some c762, some c191, some c25, some c195, some c204, some c342, some c300, some c360, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1777 : lratChecker f1777 p1777 = .success := by decide +kernel
theorem unsat1777 : Unsatisfiable (PosFin 57) f1777 := by
  apply lratCheckerSound f1777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1777
  · intro a ha; simp [p1777] at ha; subst a; trivial
  · exact checked1777
theorem derived1777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1777 := by
  apply localUnsat_implies_entails f1777 [c1761, c1768, c1773, c1772, c976, c322, c282, c1465, c762, c191, c25, c195, c204, c342, c300, c360] c1777 unsat1777 (by rfl) a
  have h0 : Entails.eval a c1761 := derived1761 a h
  have h1 : Entails.eval a c1768 := derived1768 a h
  have h2 : Entails.eval a c1773 := derived1773 a h
  have h3 : Entails.eval a c1772 := derived1772 a h
  have h4 : Entails.eval a c976 := derived976 a h
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c282 := h 281 (by decide)
  have h7 : Entails.eval a c1465 := derived1465 a h
  have h8 : Entails.eval a c762 := derived762 a h
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1778 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1763, some c1767, some c97, some c99, some c1671, some c1761, some c1776, some c50, some c1768, some c1773, some c1772, some c1777, some c1774, some c195, some c352, some c345, some c342, some c155, some c11, some c3, some c1118, some c158, some c298, some c273, some c262, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1778 : lratChecker f1778 p1778 = .success := by decide +kernel
theorem unsat1778 : Unsatisfiable (PosFin 57) f1778 := by
  apply lratCheckerSound f1778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1778
  · intro a ha; simp [p1778] at ha; subst a; trivial
  · exact checked1778
theorem derived1778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1778 := by
  apply localUnsat_implies_entails f1778 [c1763, c1767, c97, c99, c1671, c1761, c1776, c50, c1768, c1773, c1772, c1777, c1774, c195, c352, c345, c342, c155, c11, c3, c1118, c158, c298, c273, c262] c1778 unsat1778 (by rfl) a
  have h0 : Entails.eval a c1763 := derived1763 a h
  have h1 : Entails.eval a c1767 := derived1767 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1761 := derived1761 a h
  have h6 : Entails.eval a c1776 := derived1776 a h
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c1768 := derived1768 a h
  have h9 : Entails.eval a c1773 := derived1773 a h
  have h10 : Entails.eval a c1772 := derived1772 a h
  have h11 : Entails.eval a c1777 := derived1777 a h
  have h12 : Entails.eval a c1774 := derived1774 a h
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c155 := h 154 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c1118 := derived1118 a h
  have h21 : Entails.eval a c158 := h 157 (by decide)
  have h22 : Entails.eval a c298 := h 297 (by decide)
  have h23 : Entails.eval a c273 := h 272 (by decide)
  have h24 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1779 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1763, some c1767, some c97, some c99, some c1761, some c1772, some c1773, some c1776, some c50, some c1768, some c1778, some c302, some c312, some c305, some c155, some c11, some c3, some c1118, some c968, some c338, some c360, some c262, some c976, some c313, some c158, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1779 : lratChecker f1779 p1779 = .success := by decide +kernel
theorem unsat1779 : Unsatisfiable (PosFin 57) f1779 := by
  apply lratCheckerSound f1779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1779
  · intro a ha; simp [p1779] at ha; subst a; trivial
  · exact checked1779
theorem derived1779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1779 := by
  apply localUnsat_implies_entails f1779 [c1671, c1763, c1767, c97, c99, c1761, c1772, c1773, c1776, c50, c1768, c1778, c302, c312, c305, c155, c11, c3, c1118, c968, c338, c360, c262, c976, c313, c158] c1779 unsat1779 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1763 := derived1763 a h
  have h2 : Entails.eval a c1767 := derived1767 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c1761 := derived1761 a h
  have h6 : Entails.eval a c1772 := derived1772 a h
  have h7 : Entails.eval a c1773 := derived1773 a h
  have h8 : Entails.eval a c1776 := derived1776 a h
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c1768 := derived1768 a h
  have h11 : Entails.eval a c1778 := derived1778 a h
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c1118 := derived1118 a h
  have h19 : Entails.eval a c968 := derived968 a h
  have h20 : Entails.eval a c338 := h 337 (by decide)
  have h21 : Entails.eval a c360 := h 359 (by decide)
  have h22 : Entails.eval a c262 := h 261 (by decide)
  have h23 : Entails.eval a c976 := derived976 a h
  have h24 : Entails.eval a c313 := h 312 (by decide)
  have h25 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1780 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨35, by decide⟩, true), (⟨43, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c28, some c210, some c204, some c231, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1780 : lratChecker f1780 p1780 = .success := by decide +kernel
theorem unsat1780 : Unsatisfiable (PosFin 57) f1780 := by
  apply lratCheckerSound f1780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1780
  · intro a ha; simp [p1780] at ha; subst a; trivial
  · exact checked1780
theorem derived1780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1780 := by
  apply localUnsat_implies_entails f1780 [c17, c28, c210, c204, c231] c1780 unsat1780 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1780

end CochromaticTwenty.Certificates.B16_8_2
