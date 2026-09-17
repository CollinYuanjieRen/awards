import MerLeanExperiment.Certificates.B16_4_2.Steps1300_1399

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1784 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1776, some c1781, some c1282, some c1303, some c17, some c1766, some c111, some c1077, some c1777, some c353, some c1782, some c148, some c171, some c10, some c167, some c1783, some c1539, some c315, some c1760, some c45, some c339, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1784 : lratChecker f1784 p1784 = .success := by decide +kernel
theorem unsat1784 : Unsatisfiable (PosFin 57) f1784 := by
  apply lratCheckerSound f1784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1784
  · intro a ha; simp [p1784] at ha; subst a; trivial
  · exact checked1784
theorem derived1784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1784 := by
  apply localUnsat_implies_entails f1784 [c1569, c1776, c1781, c1282, c1303, c17, c1766, c111, c1077, c1777, c353, c1782, c148, c171, c10, c167, c1783, c1539, c315, c1760, c45, c339] c1784 unsat1784 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1776 := derived1776 a h
  have h2 : Entails.eval a c1781 := derived1781 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1303 := derived1303 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1766 := derived1766 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1077 := derived1077 a h
  have h9 : Entails.eval a c1777 := derived1777 a h
  have h10 : Entails.eval a c353 := h 352 (by decide)
  have h11 : Entails.eval a c1782 := derived1782 a h
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c1783 := derived1783 a h
  have h17 : Entails.eval a c1539 := derived1539 a h
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c1760 := derived1760 a h
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1785 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1766, some c1077, some c1776, some c1781, some c1282, some c1303, some c17, some c1784, some c358, some c355, some c76, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1785 : lratChecker f1785 p1785 = .success := by decide +kernel
theorem unsat1785 : Unsatisfiable (PosFin 57) f1785 := by
  apply lratCheckerSound f1785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1785
  · intro a ha; simp [p1785] at ha; subst a; trivial
  · exact checked1785
theorem derived1785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1785 := by
  apply localUnsat_implies_entails f1785 [c1569, c1766, c1077, c1776, c1781, c1282, c1303, c17, c1784, c358, c355, c76] c1785 unsat1785 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1766 := derived1766 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1776 := derived1776 a h
  have h4 : Entails.eval a c1781 := derived1781 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c1784 := derived1784 a h
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1786 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c203, some c202, some c119, some c147, some c172, some c1092, some c211, some c37, some c45, some c54, some c53, some c338, some c337, some c188, some c320, some c310, some c311, some c318, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1786 : lratChecker f1786 p1786 = .success := by decide +kernel
theorem unsat1786 : Unsatisfiable (PosFin 57) f1786 := by
  apply lratCheckerSound f1786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1786
  · intro a ha; simp [p1786] at ha; subst a; trivial
  · exact checked1786
theorem derived1786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1786 := by
  apply localUnsat_implies_entails f1786 [c1569, c1733, c203, c202, c119, c147, c172, c1092, c211, c37, c45, c54, c53, c338, c337, c188, c320, c310, c311, c318] c1786 unsat1786 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c172 := h 171 (by decide)
  have h7 : Entails.eval a c1092 := derived1092 a h
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c338 := h 337 (by decide)
  have h14 : Entails.eval a c337 := h 336 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c310 := h 309 (by decide)
  have h18 : Entails.eval a c311 := h 310 (by decide)
  have h19 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1787 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c243, some c331, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1787 : lratChecker f1787 p1787 = .success := by decide +kernel
theorem unsat1787 : Unsatisfiable (PosFin 57) f1787 := by
  apply lratCheckerSound f1787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1787
  · intro a ha; simp [p1787] at ha; subst a; trivial
  · exact checked1787
theorem derived1787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1787 := by
  apply localUnsat_implies_entails f1787 [c19, c243, c331] c1787 unsat1787 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1788 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c120, some c203, some c202, some c24, some c1785, some c112, some c1786, some c813, some c235, some c1092, some c127, some c140, some c92, some c1787, some c271, some c1641, some c233, some c136, some c12, some c207, some c815, some c582, some c160, some c773, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1788 : lratChecker f1788 p1788 = .success := by decide +kernel
theorem unsat1788 : Unsatisfiable (PosFin 57) f1788 := by
  apply lratCheckerSound f1788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1788
  · intro a ha; simp [p1788] at ha; subst a; trivial
  · exact checked1788
theorem derived1788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1788 := by
  apply localUnsat_implies_entails f1788 [c1733, c1569, c120, c203, c202, c24, c1785, c112, c1786, c813, c235, c1092, c127, c140, c92, c1787, c271, c1641, c233, c136, c12, c207, c815, c582, c160, c773] c1788 unsat1788 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1785 := derived1785 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c1786 := derived1786 a h
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c1092 := derived1092 a h
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c1787 := derived1787 a h
  have h16 : Entails.eval a c271 := h 270 (by decide)
  have h17 : Entails.eval a c1641 := derived1641 a h
  have h18 : Entails.eval a c233 := h 232 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c207 := h 206 (by decide)
  have h22 : Entails.eval a c815 := derived815 a h
  have h23 : Entails.eval a c582 := derived582 a h
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c773 := derived773 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1789 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨36, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c120, some c203, some c119, some c1673, some c1738, some c39, some c235, some c359, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1789 : lratChecker f1789 p1789 = .success := by decide +kernel
theorem unsat1789 : Unsatisfiable (PosFin 57) f1789 := by
  apply lratCheckerSound f1789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1789
  · intro a ha; simp [p1789] at ha; subst a; trivial
  · exact checked1789
theorem derived1789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1789 := by
  apply localUnsat_implies_entails f1789 [c1733, c120, c203, c119, c1673, c1738, c39, c235, c359] c1789 unsat1789 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1673 := derived1673 a h
  have h5 : Entails.eval a c1738 := derived1738 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c235 := h 234 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1790 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1785, some c112, some c120, some c203, some c1788, some c26, some c25, some c268, some c233, some c27, some c1789, some c813, some c235, some c1738, some c1740, some c136, some c39, some c12, some c218, some c145, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1790 : lratChecker f1790 p1790 = .success := by decide +kernel
theorem unsat1790 : Unsatisfiable (PosFin 57) f1790 := by
  apply lratCheckerSound f1790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1790
  · intro a ha; simp [p1790] at ha; subst a; trivial
  · exact checked1790
theorem derived1790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1790 := by
  apply localUnsat_implies_entails f1790 [c1733, c1569, c1785, c112, c120, c203, c1788, c26, c25, c268, c233, c27, c1789, c813, c235, c1738, c1740, c136, c39, c12, c218, c145] c1790 unsat1790 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c1788 := derived1788 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c1789 := derived1789 a h
  have h13 : Entails.eval a c813 := derived813 a h
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c1738 := derived1738 a h
  have h16 : Entails.eval a c1740 := derived1740 a h
  have h17 : Entails.eval a c136 := h 135 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c12 := h 11 (by decide)
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1791 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨39, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c202, some c203, some c172, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p1791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1791 : lratChecker f1791 p1791 = .success := by decide +kernel
theorem unsat1791 : Unsatisfiable (PosFin 57) f1791 := by
  apply lratCheckerSound f1791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1791
  · intro a ha; simp [p1791] at ha; subst a; trivial
  · exact checked1791
theorem derived1791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1791 := by
  apply localUnsat_implies_entails f1791 [c1733, c202, c203, c172] c1791 unsat1791 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1792 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨39, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1790, some c1590, some c1791, some c1785, some c112, some c1738, some c139, some c201, some c820, some c172, some c211, some c37, some c45, some c54, some c53, some c340, some c186, some c185, some c320, some c310, some c311, some c318, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1792 : lratChecker f1792 p1792 = .success := by decide +kernel
theorem unsat1792 : Unsatisfiable (PosFin 57) f1792 := by
  apply lratCheckerSound f1792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1792
  · intro a ha; simp [p1792] at ha; subst a; trivial
  · exact checked1792
theorem derived1792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1792 := by
  apply localUnsat_implies_entails f1792 [c1569, c1733, c1790, c1590, c1791, c1785, c112, c1738, c139, c201, c820, c172, c211, c37, c45, c54, c53, c340, c186, c185, c320, c310, c311, c318] c1792 unsat1792 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1790 := derived1790 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c1791 := derived1791 a h
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c820 := derived820 a h
  have h11 : Entails.eval a c172 := h 171 (by decide)
  have h12 : Entails.eval a c211 := h 210 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c53 := h 52 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  have h21 : Entails.eval a c310 := h 309 (by decide)
  have h22 : Entails.eval a c311 := h 310 (by decide)
  have h23 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1793 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1785, some c112, some c525, some c232, some c31, some c269, some c1620, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1793 : lratChecker f1793 p1793 = .success := by decide +kernel
theorem unsat1793 : Unsatisfiable (PosFin 57) f1793 := by
  apply lratCheckerSound f1793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1793
  · intro a ha; simp [p1793] at ha; subst a; trivial
  · exact checked1793
theorem derived1793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1793 := by
  apply localUnsat_implies_entails f1793 [c1785, c112, c525, c232, c31, c269, c1620] c1793 unsat1793 (by rfl) a
  have h0 : Entails.eval a c1785 := derived1785 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c525 := derived525 a h
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c1620 := derived1620 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1794 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨13, by decide⟩, true), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1790, some c1590, some c1791, some c139, some c128, some c1785, some c112, some c19, some c39, some c70, some c1701, some c271, some c1450, some c137, some c33, some c328, some c13, some c775, some c768, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1794 : lratChecker f1794 p1794 = .success := by decide +kernel
theorem unsat1794 : Unsatisfiable (PosFin 57) f1794 := by
  apply lratCheckerSound f1794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1794
  · intro a ha; simp [p1794] at ha; subst a; trivial
  · exact checked1794
theorem derived1794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1794 := by
  apply localUnsat_implies_entails f1794 [c1790, c1590, c1791, c139, c128, c1785, c112, c19, c39, c70, c1701, c271, c1450, c137, c33, c328, c13, c775, c768] c1794 unsat1794 (by rfl) a
  have h0 : Entails.eval a c1790 := derived1790 a h
  have h1 : Entails.eval a c1590 := derived1590 a h
  have h2 : Entails.eval a c1791 := derived1791 a h
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c1701 := derived1701 a h
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c1450 := derived1450 a h
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c328 := h 327 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c775 := derived775 a h
  have h18 : Entails.eval a c768 := derived768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1795 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1790, some c1590, some c1785, some c112, some c1791, some c1792, some c119, some c236, some c201, some c139, some c1793, some c1794, some c356, some c359, some c65, some c1641, some c693, some c135, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1795 : lratChecker f1795 p1795 = .success := by decide +kernel
theorem unsat1795 : Unsatisfiable (PosFin 57) f1795 := by
  apply lratCheckerSound f1795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1795
  · intro a ha; simp [p1795] at ha; subst a; trivial
  · exact checked1795
theorem derived1795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1795 := by
  apply localUnsat_implies_entails f1795 [c1733, c1569, c1790, c1590, c1785, c112, c1791, c1792, c119, c236, c201, c139, c1793, c1794, c356, c359, c65, c1641, c693, c135] c1795 unsat1795 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1790 := derived1790 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c1792 := derived1792 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c1793 := derived1793 a h
  have h13 : Entails.eval a c1794 := derived1794 a h
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c65 := h 64 (by decide)
  have h17 : Entails.eval a c1641 := derived1641 a h
  have h18 : Entails.eval a c693 := derived693 a h
  have h19 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1796 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨34, by decide⟩, false), (⟨39, by decide⟩, false), (⟨17, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c355, some c1785, some c112, some c66, some c356, some c67, some c37, some c813, some c117, some c234, some c201, some c12, some c210, some c146, some c282, some c202, some c892, some c128, some c47, some c336, some c328, some c347, some c341, some c365, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1796 : lratChecker f1796 p1796 = .success := by decide +kernel
theorem unsat1796 : Unsatisfiable (PosFin 57) f1796 := by
  apply lratCheckerSound f1796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1796
  · intro a ha; simp [p1796] at ha; subst a; trivial
  · exact checked1796
theorem derived1796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1796 := by
  apply localUnsat_implies_entails f1796 [c1569, c1733, c355, c1785, c112, c66, c356, c67, c37, c813, c117, c234, c201, c12, c210, c146, c282, c202, c892, c128, c47, c336, c328, c347, c341, c365] c1796 unsat1796 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c892 := derived892 a h
  have h19 : Entails.eval a c128 := h 127 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  have h22 : Entails.eval a c328 := h 327 (by decide)
  have h23 : Entails.eval a c347 := h 346 (by decide)
  have h24 : Entails.eval a c341 := h 340 (by decide)
  have h25 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1797 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1790, some c1590, some c1785, some c112, some c1795, some c813, some c355, some c66, some c65, some c356, some c1796, some c1738, some c1034, some c145, some c201, some c1414, some c127, some c271, some c336, some c331, some c243, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1797 : lratChecker f1797 p1797 = .success := by decide +kernel
theorem unsat1797 : Unsatisfiable (PosFin 57) f1797 := by
  apply lratCheckerSound f1797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1797
  · intro a ha; simp [p1797] at ha; subst a; trivial
  · exact checked1797
theorem derived1797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1797 := by
  apply localUnsat_implies_entails f1797 [c1569, c1733, c1790, c1590, c1785, c112, c1795, c813, c355, c66, c65, c356, c1796, c1738, c1034, c145, c201, c1414, c127, c271, c336, c331, c243] c1797 unsat1797 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1790 := derived1790 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1795 := derived1795 a h
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c1796 := derived1796 a h
  have h13 : Entails.eval a c1738 := derived1738 a h
  have h14 : Entails.eval a c1034 := derived1034 a h
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c1414 := derived1414 a h
  have h18 : Entails.eval a c127 := h 126 (by decide)
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c331 := h 330 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1798 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c112, some c1790, some c1590, some c1797, some c26, some c17, some c25, some c355, some c268, some c1791, some c27, some c137, some c12, some c139, some c1794, some c1738, some c525, some c359, some c236, some c356, some c170, some c1512, some c13, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1798 : lratChecker f1798 p1798 = .success := by decide +kernel
theorem unsat1798 : Unsatisfiable (PosFin 57) f1798 := by
  apply lratCheckerSound f1798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1798
  · intro a ha; simp [p1798] at ha; subst a; trivial
  · exact checked1798
theorem derived1798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1798 := by
  apply localUnsat_implies_entails f1798 [c1569, c1785, c112, c1790, c1590, c1797, c26, c17, c25, c355, c268, c1791, c27, c137, c12, c139, c1794, c1738, c525, c359, c236, c356, c170, c1512, c13] c1798 unsat1798 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1790 := derived1790 a h
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c1797 := derived1797 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1791 := derived1791 a h
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c1794 := derived1794 a h
  have h17 : Entails.eval a c1738 := derived1738 a h
  have h18 : Entails.eval a c525 := derived525 a h
  have h19 : Entails.eval a c359 := h 358 (by decide)
  have h20 : Entails.eval a c236 := h 235 (by decide)
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c170 := h 169 (by decide)
  have h23 : Entails.eval a c1512 := derived1512 a h
  have h24 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1799 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c267, some c266, some c1786, some c119, some c236, some c148, some c1763, some c212, some c37, some c45, some c54, some c53, some c338, some c187, some c337, some c318, some c312, some c310, some c320, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1799 : lratChecker f1799 p1799 = .success := by decide +kernel
theorem unsat1799 : Unsatisfiable (PosFin 57) f1799 := by
  apply lratCheckerSound f1799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1799
  · intro a ha; simp [p1799] at ha; subst a; trivial
  · exact checked1799
theorem derived1799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1799 := by
  apply localUnsat_implies_entails f1799 [c1569, c1733, c267, c266, c1786, c119, c236, c148, c1763, c212, c37, c45, c54, c53, c338, c187, c337, c318, c312, c310, c320] c1799 unsat1799 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1786 := derived1786 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c1763 := derived1763 a h
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c187 := h 186 (by decide)
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c310 := h 309 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1800 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c17, some c1785, some c112, some c26, some c202, some c1791, some c715, some c126, some c541, some c1414, some c333, some c239, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1800 : lratChecker f1800 p1800 = .success := by decide +kernel
theorem unsat1800 : Unsatisfiable (PosFin 57) f1800 := by
  apply lratCheckerSound f1800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1800
  · intro a ha; simp [p1800] at ha; subst a; trivial
  · exact checked1800
theorem derived1800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1800 := by
  apply localUnsat_implies_entails f1800 [c1569, c1733, c17, c1785, c112, c26, c202, c1791, c715, c126, c541, c1414, c333, c239] c1800 unsat1800 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c1791 := derived1791 a h
  have h8 : Entails.eval a c715 := derived715 a h
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c541 := derived541 a h
  have h11 : Entails.eval a c1414 := derived1414 a h
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1801 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c27, some c17, some c1785, some c112, some c1738, some c685, some c820, some c125, some c532, some c88, some c239, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1801 : lratChecker f1801 p1801 = .success := by decide +kernel
theorem unsat1801 : Unsatisfiable (PosFin 57) f1801 := by
  apply lratCheckerSound f1801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1801
  · intro a ha; simp [p1801] at ha; subst a; trivial
  · exact checked1801
theorem derived1801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1801 := by
  apply localUnsat_implies_entails f1801 [c1569, c27, c17, c1785, c112, c1738, c685, c820, c125, c532, c88, c239] c1801 unsat1801 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1738 := derived1738 a h
  have h6 : Entails.eval a c685 := derived685 a h
  have h7 : Entails.eval a c820 := derived820 a h
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c532 := derived532 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1802 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1798, some c1785, some c112, some c1799, some c26, some c25, some c270, some c268, some c1800, some c148, some c216, some c38, some c53, some c1278, some c1801, some c357, some c232, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1802 : lratChecker f1802 p1802 = .success := by decide +kernel
theorem unsat1802 : Unsatisfiable (PosFin 57) f1802 := by
  apply lratCheckerSound f1802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1802
  · intro a ha; simp [p1802] at ha; subst a; trivial
  · exact checked1802
theorem derived1802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1802 := by
  apply localUnsat_implies_entails f1802 [c1569, c1798, c1785, c112, c1799, c26, c25, c270, c268, c1800, c148, c216, c38, c53, c1278, c1801, c357, c232] c1802 unsat1802 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1798 := derived1798 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1799 := derived1799 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c1800 := derived1800 a h
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c1278 := derived1278 a h
  have h15 : Entails.eval a c1801 := derived1801 a h
  have h16 : Entails.eval a c357 := h 356 (by decide)
  have h17 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1803 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c813, some c1763, some c1436, some c202, some c148, some c171, some c212, some c37, some c45, some c54, some c53, some c339, some c186, some c185, some c318, some c312, some c310, some c320, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1803 : lratChecker f1803 p1803 = .success := by decide +kernel
theorem unsat1803 : Unsatisfiable (PosFin 57) f1803 := by
  apply lratCheckerSound f1803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1803
  · intro a ha; simp [p1803] at ha; subst a; trivial
  · exact checked1803
theorem derived1803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1803 := by
  apply localUnsat_implies_entails f1803 [c1569, c1733, c813, c1763, c1436, c202, c148, c171, c212, c37, c45, c54, c53, c339, c186, c185, c318, c312, c310, c320] c1803 unsat1803 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c1763 := derived1763 a h
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c339 := h 338 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c310 := h 309 (by decide)
  have h19 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1804 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1798, some c1785, some c112, some c1802, some c1803, some c25, some c270, some c813, some c1763, some c118, some c140, some c1753, some c1738, some c117, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1804 : lratChecker f1804 p1804 = .success := by decide +kernel
theorem unsat1804 : Unsatisfiable (PosFin 57) f1804 := by
  apply lratCheckerSound f1804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1804
  · intro a ha; simp [p1804] at ha; subst a; trivial
  · exact checked1804
theorem derived1804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1804 := by
  apply localUnsat_implies_entails f1804 [c1569, c1798, c1785, c112, c1802, c1803, c25, c270, c813, c1763, c118, c140, c1753, c1738, c117] c1804 unsat1804 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1798 := derived1798 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1802 := derived1802 a h
  have h5 : Entails.eval a c1803 := derived1803 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1763 := derived1763 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  have h12 : Entails.eval a c1753 := derived1753 a h
  have h13 : Entails.eval a c1738 := derived1738 a h
  have h14 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1805 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1798, some c1785, some c112, some c1802, some c813, some c1763, some c1803, some c26, some c25, some c270, some c268, some c27, some c1804, some c202, some c171, some c1753, some c12, some c234, some c136, some c1738, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1805 : lratChecker f1805 p1805 = .success := by decide +kernel
theorem unsat1805 : Unsatisfiable (PosFin 57) f1805 := by
  apply lratCheckerSound f1805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1805
  · intro a ha; simp [p1805] at ha; subst a; trivial
  · exact checked1805
theorem derived1805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1805 := by
  apply localUnsat_implies_entails f1805 [c1569, c1733, c1798, c1785, c112, c1802, c813, c1763, c1803, c26, c25, c270, c268, c27, c1804, c202, c171, c1753, c12, c234, c136, c1738] c1805 unsat1805 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1798 := derived1798 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1802 := derived1802 a h
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c1803 := derived1803 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c1804 := derived1804 a h
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c171 := h 170 (by decide)
  have h17 : Entails.eval a c1753 := derived1753 a h
  have h18 : Entails.eval a c12 := h 11 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c136 := h 135 (by decide)
  have h21 : Entails.eval a c1738 := derived1738 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1806 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1805, some c1590, some c1798, some c1785, some c112, some c267, some c266, some c236, some c118, some c22, some c813, some c355, some c202, some c234, some c66, some c65, some c1034, some c356, some c145, some c67, some c201, some c1414, some c12, some c127, some c271, some c336, some c331, some c181, some c242, some c89, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1806 : lratChecker f1806 p1806 = .success := by decide +kernel
theorem unsat1806 : Unsatisfiable (PosFin 57) f1806 := by
  apply lratCheckerSound f1806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1806
  · intro a ha; simp [p1806] at ha; subst a; trivial
  · exact checked1806
theorem derived1806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1806 := by
  apply localUnsat_implies_entails f1806 [c1569, c1733, c1805, c1590, c1798, c1785, c112, c267, c266, c236, c118, c22, c813, c355, c202, c234, c66, c65, c1034, c356, c145, c67, c201, c1414, c12, c127, c271, c336, c331, c181, c242, c89] c1806 unsat1806 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1805 := derived1805 a h
  have h3 : Entails.eval a c1590 := derived1590 a h
  have h4 : Entails.eval a c1798 := derived1798 a h
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c813 := derived813 a h
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c1034 := derived1034 a h
  have h19 : Entails.eval a c356 := h 355 (by decide)
  have h20 : Entails.eval a c145 := h 144 (by decide)
  have h21 : Entails.eval a c67 := h 66 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  have h23 : Entails.eval a c1414 := derived1414 a h
  have h24 : Entails.eval a c12 := h 11 (by decide)
  have h25 : Entails.eval a c127 := h 126 (by decide)
  have h26 : Entails.eval a c271 := h 270 (by decide)
  have h27 : Entails.eval a c336 := h 335 (by decide)
  have h28 : Entails.eval a c331 := h 330 (by decide)
  have h29 : Entails.eval a c181 := h 180 (by decide)
  have h30 : Entails.eval a c242 := h 241 (by decide)
  have h31 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1807 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c112, some c1798, some c1805, some c1590, some c1806, some c26, some c17, some c25, some c355, some c270, some c268, some c236, some c118, some c22, some c27, some c1738, some c13, some c234, some c124, some c767, some c89, some c246, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1807 : lratChecker f1807 p1807 = .success := by decide +kernel
theorem unsat1807 : Unsatisfiable (PosFin 57) f1807 := by
  apply lratCheckerSound f1807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1807
  · intro a ha; simp [p1807] at ha; subst a; trivial
  · exact checked1807
theorem derived1807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1807 := by
  apply localUnsat_implies_entails f1807 [c1569, c1785, c112, c1798, c1805, c1590, c1806, c26, c17, c25, c355, c270, c268, c236, c118, c22, c27, c1738, c13, c234, c124, c767, c89, c246] c1807 unsat1807 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1798 := derived1798 a h
  have h4 : Entails.eval a c1805 := derived1805 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c1806 := derived1806 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c1738 := derived1738 a h
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c767 := derived767 a h
  have h22 : Entails.eval a c89 := h 88 (by decide)
  have h23 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1808 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c120, some c203, some c1807, some c24, some c8, some c1282, some c1785, some c112, some c1791, some c119, some c165, some c147, some c357, some c211, some c233, some c54, some c1673, some c19, some c30, some c1425, some c269, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1808 : lratChecker f1808 p1808 = .success := by decide +kernel
theorem unsat1808 : Unsatisfiable (PosFin 57) f1808 := by
  apply lratCheckerSound f1808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1808
  · intro a ha; simp [p1808] at ha; subst a; trivial
  · exact checked1808
theorem derived1808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1808 := by
  apply localUnsat_implies_entails f1808 [c1733, c1569, c120, c203, c1807, c24, c8, c1282, c1785, c112, c1791, c119, c165, c147, c357, c211, c233, c54, c1673, c19, c30, c1425, c269] c1808 unsat1808 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c1807 := derived1807 a h
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c1785 := derived1785 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c1791 := derived1791 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c233 := h 232 (by decide)
  have h17 : Entails.eval a c54 := h 53 (by decide)
  have h18 : Entails.eval a c1673 := derived1673 a h
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c30 := h 29 (by decide)
  have h21 : Entails.eval a c1425 := derived1425 a h
  have h22 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1809 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c120, some c203, some c202, some c1807, some c24, some c8, some c1282, some c1785, some c112, some c1808, some c813, some c1092, some c133, some c140, some c1748, some c269, some c66, some c1150, some c70, some c233, some c357, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1809 : lratChecker f1809 p1809 = .success := by decide +kernel
theorem unsat1809 : Unsatisfiable (PosFin 57) f1809 := by
  apply lratCheckerSound f1809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1809
  · intro a ha; simp [p1809] at ha; subst a; trivial
  · exact checked1809
theorem derived1809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1809 := by
  apply localUnsat_implies_entails f1809 [c1733, c1569, c120, c203, c202, c1807, c24, c8, c1282, c1785, c112, c1808, c813, c1092, c133, c140, c1748, c269, c66, c1150, c70, c233, c357] c1809 unsat1809 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1807 := derived1807 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1785 := derived1785 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c1808 := derived1808 a h
  have h12 : Entails.eval a c813 := derived813 a h
  have h13 : Entails.eval a c1092 := derived1092 a h
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c1748 := derived1748 a h
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c66 := h 65 (by decide)
  have h19 : Entails.eval a c1150 := derived1150 a h
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  have h22 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1810 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1785, some c112, some c1809, some c26, some c120, some c203, some c1807, some c24, some c8, some c1282, some c119, some c165, some c147, some c1789, some c1673, some c1738, some c233, some c168, some c39, some c47, some c54, some c58, some c235, some c638, some c341, some c346, some c257, some c313, some c12, some c304, some c48, some c317, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1810 : lratChecker f1810 p1810 = .success := by decide +kernel
theorem unsat1810 : Unsatisfiable (PosFin 57) f1810 := by
  apply lratCheckerSound f1810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1810
  · intro a ha; simp [p1810] at ha; subst a; trivial
  · exact checked1810
theorem derived1810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1810 := by
  apply localUnsat_implies_entails f1810 [c1733, c1569, c1785, c112, c1809, c26, c120, c203, c1807, c24, c8, c1282, c119, c165, c147, c1789, c1673, c1738, c233, c168, c39, c47, c54, c58, c235, c638, c341, c346, c257, c313, c12, c304, c48, c317] c1810 unsat1810 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1809 := derived1809 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c1807 := derived1807 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c1282 := derived1282 a h
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c1789 := derived1789 a h
  have h16 : Entails.eval a c1673 := derived1673 a h
  have h17 : Entails.eval a c1738 := derived1738 a h
  have h18 : Entails.eval a c233 := h 232 (by decide)
  have h19 : Entails.eval a c168 := h 167 (by decide)
  have h20 : Entails.eval a c39 := h 38 (by decide)
  have h21 : Entails.eval a c47 := h 46 (by decide)
  have h22 : Entails.eval a c54 := h 53 (by decide)
  have h23 : Entails.eval a c58 := h 57 (by decide)
  have h24 : Entails.eval a c235 := h 234 (by decide)
  have h25 : Entails.eval a c638 := derived638 a h
  have h26 : Entails.eval a c341 := h 340 (by decide)
  have h27 : Entails.eval a c346 := h 345 (by decide)
  have h28 : Entails.eval a c257 := h 256 (by decide)
  have h29 : Entails.eval a c313 := h 312 (by decide)
  have h30 : Entails.eval a c12 := h 11 (by decide)
  have h31 : Entails.eval a c304 := h 303 (by decide)
  have h32 : Entails.eval a c48 := h 47 (by decide)
  have h33 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1811 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1807, some c1282, some c1785, some c112, some c24, some c120, some c8, some c202, some c203, some c1809, some c26, some c17, some c1810, some c813, some c235, some c1738, some c521, some c271, some c133, some c233, some c136, some c1160, some c754, some c357, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1811 : lratChecker f1811 p1811 = .success := by decide +kernel
theorem unsat1811 : Unsatisfiable (PosFin 57) f1811 := by
  apply lratCheckerSound f1811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1811
  · intro a ha; simp [p1811] at ha; subst a; trivial
  · exact checked1811
theorem derived1811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1811 := by
  apply localUnsat_implies_entails f1811 [c1733, c1569, c1807, c1282, c1785, c112, c24, c120, c8, c202, c203, c1809, c26, c17, c1810, c813, c235, c1738, c521, c271, c133, c233, c136, c1160, c754, c357] c1811 unsat1811 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1807 := derived1807 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c1809 := derived1809 a h
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c1810 := derived1810 a h
  have h15 : Entails.eval a c813 := derived813 a h
  have h16 : Entails.eval a c235 := h 234 (by decide)
  have h17 : Entails.eval a c1738 := derived1738 a h
  have h18 : Entails.eval a c521 := derived521 a h
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  have h22 : Entails.eval a c136 := h 135 (by decide)
  have h23 : Entails.eval a c1160 := derived1160 a h
  have h24 : Entails.eval a c754 := derived754 a h
  have h25 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1812 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c203, some c1791, some c147, some c354, some c211, some c37, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1812 : lratChecker f1812 p1812 = .success := by decide +kernel
theorem unsat1812 : Unsatisfiable (PosFin 57) f1812 := by
  apply lratCheckerSound f1812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1812
  · intro a ha; simp [p1812] at ha; subst a; trivial
  · exact checked1812
theorem derived1812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1812 := by
  apply localUnsat_implies_entails f1812 [c1733, c1569, c203, c1791, c147, c354, c211, c37] c1812 unsat1812 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c1791 := derived1791 a h
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1813 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1811, some c1807, some c1282, some c1785, some c112, some c1738, some c1812, some c128, some c139, some c820, some c211, some c37, some c45, some c54, some c354, some c340, some c251, some c185, some c320, some c22, some c42, some c311, some c250, some c299, some c300, some c370, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1813 : lratChecker f1813 p1813 = .success := by decide +kernel
theorem unsat1813 : Unsatisfiable (PosFin 57) f1813 := by
  apply lratCheckerSound f1813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1813
  · intro a ha; simp [p1813] at ha; subst a; trivial
  · exact checked1813
theorem derived1813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1813 := by
  apply localUnsat_implies_entails f1813 [c1569, c1733, c1811, c1807, c1282, c1785, c112, c1738, c1812, c128, c139, c820, c211, c37, c45, c54, c354, c340, c251, c185, c320, c22, c42, c311, c250, c299, c300, c370] c1813 unsat1813 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1811 := derived1811 a h
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1812 := derived1812 a h
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c820 := derived820 a h
  have h12 : Entails.eval a c211 := h 210 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c340 := h 339 (by decide)
  have h18 : Entails.eval a c251 := h 250 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  have h21 : Entails.eval a c22 := h 21 (by decide)
  have h22 : Entails.eval a c42 := h 41 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  have h24 : Entails.eval a c250 := h 249 (by decide)
  have h25 : Entails.eval a c299 := h 298 (by decide)
  have h26 : Entails.eval a c300 := h 299 (by decide)
  have h27 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1814 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨23, by decide⟩, true), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c119, some c201, some c203, some c139, some c1811, some c1807, some c1282, some c1785, some c112, some c66, some c1034, some c145, some c1431, some c359, some c30, some c1793, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1814 : lratChecker f1814 p1814 = .success := by decide +kernel
theorem unsat1814 : Unsatisfiable (PosFin 57) f1814 := by
  apply lratCheckerSound f1814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1814
  · intro a ha; simp [p1814] at ha; subst a; trivial
  · exact checked1814
theorem derived1814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1814 := by
  apply localUnsat_implies_entails f1814 [c1733, c1569, c119, c201, c203, c139, c1811, c1807, c1282, c1785, c112, c66, c1034, c145, c1431, c359, c30, c1793] c1814 unsat1814 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c1811 := derived1811 a h
  have h7 : Entails.eval a c1807 := derived1807 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1785 := derived1785 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c1034 := derived1034 a h
  have h13 : Entails.eval a c145 := h 144 (by decide)
  have h14 : Entails.eval a c1431 := derived1431 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c1793 := derived1793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1815 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1811, some c1807, some c1282, some c1785, some c112, some c119, some c201, some c203, some c139, some c1814, some c354, some c70, some c22, some c1609, some c1793, some c229, some c356, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1815 : lratChecker f1815 p1815 = .success := by decide +kernel
theorem unsat1815 : Unsatisfiable (PosFin 57) f1815 := by
  apply lratCheckerSound f1815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1815
  · intro a ha; simp [p1815] at ha; subst a; trivial
  · exact checked1815
theorem derived1815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1815 := by
  apply localUnsat_implies_entails f1815 [c1733, c1811, c1807, c1282, c1785, c112, c119, c201, c203, c139, c1814, c354, c70, c22, c1609, c1793, c229, c356] c1815 unsat1815 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1811 := derived1811 a h
  have h2 : Entails.eval a c1807 := derived1807 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c1814 := derived1814 a h
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c1609 := derived1609 a h
  have h15 : Entails.eval a c1793 := derived1793 a h
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1816 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1811, some c1807, some c1282, some c1785, some c112, some c1815, some c1738, some c1813, some c26, some c17, some c354, some c70, some c22, some c42, some c1791, some c139, some c201, some c1673, some c172, some c839, some c793, some c1001, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1816 : lratChecker f1816 p1816 = .success := by decide +kernel
theorem unsat1816 : Unsatisfiable (PosFin 57) f1816 := by
  apply lratCheckerSound f1816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1816
  · intro a ha; simp [p1816] at ha; subst a; trivial
  · exact checked1816
theorem derived1816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1816 := by
  apply localUnsat_implies_entails f1816 [c1569, c1733, c1811, c1807, c1282, c1785, c112, c1815, c1738, c1813, c26, c17, c354, c70, c22, c42, c1791, c139, c201, c1673, c172, c839, c793, c1001] c1816 unsat1816 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1811 := derived1811 a h
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c1815 := derived1815 a h
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c1813 := derived1813 a h
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c1791 := derived1791 a h
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c201 := h 200 (by decide)
  have h19 : Entails.eval a c1673 := derived1673 a h
  have h20 : Entails.eval a c172 := h 171 (by decide)
  have h21 : Entails.eval a c839 := derived839 a h
  have h22 : Entails.eval a c793 := derived793 a h
  have h23 : Entails.eval a c1001 := derived1001 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1817 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1811, some c358, some c1785, some c112, some c1816, some c813, some c1738, some c117, some c201, some c355, some c37, some c17, some c211, some c1807, some c1282, some c160, some c210, some c30, some c126, some c1138, some c335, some c1414, some c245, some c333, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1817 : lratChecker f1817 p1817 = .success := by decide +kernel
theorem unsat1817 : Unsatisfiable (PosFin 57) f1817 := by
  apply lratCheckerSound f1817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1817
  · intro a ha; simp [p1817] at ha; subst a; trivial
  · exact checked1817
theorem derived1817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1817 := by
  apply localUnsat_implies_entails f1817 [c1569, c1733, c1811, c358, c1785, c112, c1816, c813, c1738, c117, c201, c355, c37, c17, c211, c1807, c1282, c160, c210, c30, c126, c1138, c335, c1414, c245, c333] c1817 unsat1817 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1811 := derived1811 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1816 := derived1816 a h
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c211 := h 210 (by decide)
  have h15 : Entails.eval a c1807 := derived1807 a h
  have h16 : Entails.eval a c1282 := derived1282 a h
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c30 := h 29 (by decide)
  have h20 : Entails.eval a c126 := h 125 (by decide)
  have h21 : Entails.eval a c1138 := derived1138 a h
  have h22 : Entails.eval a c335 := h 334 (by decide)
  have h23 : Entails.eval a c1414 := derived1414 a h
  have h24 : Entails.eval a c245 := h 244 (by decide)
  have h25 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1818 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, false), (⟨13, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c202, some c1811, some c1816, some c355, some c17, some c37, some c1807, some c1282, some c210, some c269, some c50, some c137, some c250, some c197, some c12, some c95, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1818 : lratChecker f1818 p1818 = .success := by decide +kernel
theorem unsat1818 : Unsatisfiable (PosFin 57) f1818 := by
  apply lratCheckerSound f1818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1818
  · intro a ha; simp [p1818] at ha; subst a; trivial
  · exact checked1818
theorem derived1818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1818 := by
  apply localUnsat_implies_entails f1818 [c1733, c1569, c202, c1811, c1816, c355, c17, c37, c1807, c1282, c210, c269, c50, c137, c250, c197, c12, c95] c1818 unsat1818 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c1811 := derived1811 a h
  have h4 : Entails.eval a c1816 := derived1816 a h
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c1807 := derived1807 a h
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c250 := h 249 (by decide)
  have h15 : Entails.eval a c197 := h 196 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1819 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1785, some c112, some c1816, some c813, some c1738, some c117, some c201, some c1811, some c1807, some c1282, some c358, some c228, some c1817, some c202, some c128, some c336, some c1818, some c30, some c1138, some c137, some c205, some c1391, some c177, some c84, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1819 : lratChecker f1819 p1819 = .success := by decide +kernel
theorem unsat1819 : Unsatisfiable (PosFin 57) f1819 := by
  apply lratCheckerSound f1819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1819
  · intro a ha; simp [p1819] at ha; subst a; trivial
  · exact checked1819
theorem derived1819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1819 := by
  apply localUnsat_implies_entails f1819 [c1569, c1733, c1785, c112, c1816, c813, c1738, c117, c201, c1811, c1807, c1282, c358, c228, c1817, c202, c128, c336, c1818, c30, c1138, c137, c205, c1391, c177, c84] c1819 unsat1819 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1816 := derived1816 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c1811 := derived1811 a h
  have h10 : Entails.eval a c1807 := derived1807 a h
  have h11 : Entails.eval a c1282 := derived1282 a h
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c1817 := derived1817 a h
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c1818 := derived1818 a h
  have h19 : Entails.eval a c30 := h 29 (by decide)
  have h20 : Entails.eval a c1138 := derived1138 a h
  have h21 : Entails.eval a c137 := h 136 (by decide)
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c1391 := derived1391 a h
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1820 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨33, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c17, some c37, some c22, some c42, some c210, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1820 : lratChecker f1820 p1820 = .success := by decide +kernel
theorem unsat1820 : Unsatisfiable (PosFin 57) f1820 := by
  apply lratCheckerSound f1820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1820
  · intro a ha; simp [p1820] at ha; subst a; trivial
  · exact checked1820
theorem derived1820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1820 := by
  apply localUnsat_implies_entails f1820 [c1569, c17, c37, c22, c42, c210] c1820 unsat1820 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1821 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1807, some c1282, some c1811, some c1816, some c355, some c1820, some c1819, some c358, some c17, some c37, some c1785, some c112, some c813, some c202, some c203, some c140, some c127, some c210, some c336, some c50, some c160, some c58, some c1787, some c351, some c315, some c1360, some c52, some c1605, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1821 : lratChecker f1821 p1821 = .success := by decide +kernel
theorem unsat1821 : Unsatisfiable (PosFin 57) f1821 := by
  apply lratCheckerSound f1821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1821
  · intro a ha; simp [p1821] at ha; subst a; trivial
  · exact checked1821
theorem derived1821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1821 := by
  apply localUnsat_implies_entails f1821 [c1569, c1733, c1807, c1282, c1811, c1816, c355, c1820, c1819, c358, c17, c37, c1785, c112, c813, c202, c203, c140, c127, c210, c336, c50, c160, c58, c1787, c351, c315, c1360, c52, c1605] c1821 unsat1821 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1807 := derived1807 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1811 := derived1811 a h
  have h5 : Entails.eval a c1816 := derived1816 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c1820 := derived1820 a h
  have h8 : Entails.eval a c1819 := derived1819 a h
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c1785 := derived1785 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c127 := h 126 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c50 := h 49 (by decide)
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c58 := h 57 (by decide)
  have h24 : Entails.eval a c1787 := derived1787 a h
  have h25 : Entails.eval a c351 := h 350 (by decide)
  have h26 : Entails.eval a c315 := h 314 (by decide)
  have h27 : Entails.eval a c1360 := derived1360 a h
  have h28 : Entails.eval a c52 := h 51 (by decide)
  have h29 : Entails.eval a c1605 := derived1605 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1822 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1807, some c1282, some c1785, some c112, some c1811, some c1816, some c813, some c355, some c1820, some c1819, some c1821, some c128, some c336, some c127, some c201, some c139, some c145, some c1034, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1822 : lratChecker f1822 p1822 = .success := by decide +kernel
theorem unsat1822 : Unsatisfiable (PosFin 57) f1822 := by
  apply lratCheckerSound f1822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1822
  · intro a ha; simp [p1822] at ha; subst a; trivial
  · exact checked1822
theorem derived1822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1822 := by
  apply localUnsat_implies_entails f1822 [c1733, c1569, c1807, c1282, c1785, c112, c1811, c1816, c813, c355, c1820, c1819, c1821, c128, c336, c127, c201, c139, c145, c1034] c1822 unsat1822 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1807 := derived1807 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1811 := derived1811 a h
  have h7 : Entails.eval a c1816 := derived1816 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c1820 := derived1820 a h
  have h11 : Entails.eval a c1819 := derived1819 a h
  have h12 : Entails.eval a c1821 := derived1821 a h
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c145 := h 144 (by decide)
  have h19 : Entails.eval a c1034 := derived1034 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1823 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1785, some c112, some c1822, some c267, some c26, some c1807, some c1282, some c203, some c147, some c1673, some c224, some c39, some c47, some c54, some c58, some c59, some c313, some c8, some c283, some c165, some c359, some c346, some c341, some c281, some c304, some c317, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1823 : lratChecker f1823 p1823 = .success := by decide +kernel
theorem unsat1823 : Unsatisfiable (PosFin 57) f1823 := by
  apply lratCheckerSound f1823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1823
  · intro a ha; simp [p1823] at ha; subst a; trivial
  · exact checked1823
theorem derived1823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1823 := by
  apply localUnsat_implies_entails f1823 [c1733, c1569, c1785, c112, c1822, c267, c26, c1807, c1282, c203, c147, c1673, c224, c39, c47, c54, c58, c59, c313, c8, c283, c165, c359, c346, c341, c281, c304, c317] c1823 unsat1823 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c1822 := derived1822 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1807 := derived1807 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c1673 := derived1673 a h
  have h12 : Entails.eval a c224 := h 223 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c8 := h 7 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c359 := h 358 (by decide)
  have h23 : Entails.eval a c346 := h 345 (by decide)
  have h24 : Entails.eval a c341 := h 340 (by decide)
  have h25 : Entails.eval a c281 := h 280 (by decide)
  have h26 : Entails.eval a c304 := h 303 (by decide)
  have h27 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1824 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1822, some c267, some c17, some c1785, some c112, some c26, some c1738, some c1823, some c1801, some c685, some c268, some c147, some c820, some c1763, some c734, some c125, some c532, some c132, some c167, some c330, some c237, some c1243, some c179, some c376, some c169, some c178, some c205, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1824 : lratChecker f1824 p1824 = .success := by decide +kernel
theorem unsat1824 : Unsatisfiable (PosFin 57) f1824 := by
  apply lratCheckerSound f1824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1824
  · intro a ha; simp [p1824] at ha; subst a; trivial
  · exact checked1824
theorem derived1824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1824 := by
  apply localUnsat_implies_entails f1824 [c1569, c1822, c267, c17, c1785, c112, c26, c1738, c1823, c1801, c685, c268, c147, c820, c1763, c734, c125, c532, c132, c167, c330, c237, c1243, c179, c376, c169, c178, c205] c1824 unsat1824 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1822 := derived1822 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1823 := derived1823 a h
  have h9 : Entails.eval a c1801 := derived1801 a h
  have h10 : Entails.eval a c685 := derived685 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c820 := derived820 a h
  have h14 : Entails.eval a c1763 := derived1763 a h
  have h15 : Entails.eval a c734 := derived734 a h
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c532 := derived532 a h
  have h18 : Entails.eval a c132 := h 131 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c330 := h 329 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c1243 := derived1243 a h
  have h23 : Entails.eval a c179 := h 178 (by decide)
  have h24 : Entails.eval a c376 := h 375 (by decide)
  have h25 : Entails.eval a c169 := h 168 (by decide)
  have h26 : Entails.eval a c178 := h 177 (by decide)
  have h27 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1825 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨55, by decide⟩, true), (⟨20, by decide⟩, false), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1822, some c267, some c17, some c1785, some c112, some c26, some c1807, some c1282, some c45, some c54, some c338, some c219, some c217, some c98, some c308, some c257, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1825 : lratChecker f1825 p1825 = .success := by decide +kernel
theorem unsat1825 : Unsatisfiable (PosFin 57) f1825 := by
  apply lratCheckerSound f1825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1825
  · intro a ha; simp [p1825] at ha; subst a; trivial
  · exact checked1825
theorem derived1825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1825 := by
  apply localUnsat_implies_entails f1825 [c1569, c1822, c267, c17, c1785, c112, c26, c1807, c1282, c45, c54, c338, c219, c217, c98, c308, c257] c1825 unsat1825 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1822 := derived1822 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c1807 := derived1807 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1826 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨37, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c224, some c313, some c283, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1826 : lratChecker f1826 p1826 = .success := by decide +kernel
theorem unsat1826 : Unsatisfiable (PosFin 57) f1826 := by
  apply lratCheckerSound f1826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1826
  · intro a ha; simp [p1826] at ha; subst a; trivial
  · exact checked1826
theorem derived1826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1826 := by
  apply localUnsat_implies_entails f1826 [c224, c313, c283] c1826 unsat1826 (by rfl) a
  have h0 : Entails.eval a c224 := h 223 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1827 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c112, some c1738, some c1824, some c813, some c117, some c1763, some c1822, some c267, some c17, some c1807, some c1282, some c270, some c228, some c357, some c1414, some c1423, some c1759, some c1825, some c1826, some c160, some c223, some c221, some c281, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1827 : lratChecker f1827 p1827 = .success := by decide +kernel
theorem unsat1827 : Unsatisfiable (PosFin 57) f1827 := by
  apply lratCheckerSound f1827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1827
  · intro a ha; simp [p1827] at ha; subst a; trivial
  · exact checked1827
theorem derived1827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1827 := by
  apply localUnsat_implies_entails f1827 [c1569, c1785, c112, c1738, c1824, c813, c117, c1763, c1822, c267, c17, c1807, c1282, c270, c228, c357, c1414, c1423, c1759, c1825, c1826, c160, c223, c221, c281] c1827 unsat1827 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c1824 := derived1824 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c1822 := derived1822 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c1807 := derived1807 a h
  have h12 : Entails.eval a c1282 := derived1282 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c1414 := derived1414 a h
  have h17 : Entails.eval a c1423 := derived1423 a h
  have h18 : Entails.eval a c1759 := derived1759 a h
  have h19 : Entails.eval a c1825 := derived1825 a h
  have h20 : Entails.eval a c1826 := derived1826 a h
  have h21 : Entails.eval a c160 := h 159 (by decide)
  have h22 : Entails.eval a c223 := h 222 (by decide)
  have h23 : Entails.eval a c221 := h 220 (by decide)
  have h24 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1828 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨37, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c1138, some c237, some c327, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1828 : lratChecker f1828 p1828 = .success := by decide +kernel
theorem unsat1828 : Unsatisfiable (PosFin 57) f1828 := by
  apply lratCheckerSound f1828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1828
  · intro a ha; simp [p1828] at ha; subst a; trivial
  · exact checked1828
theorem derived1828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1828 := by
  apply localUnsat_implies_entails f1828 [c268, c1138, c237, c327] c1828 unsat1828 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c1138 := derived1138 a h
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1829 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c112, some c1738, some c1824, some c813, some c117, some c1822, some c267, some c17, some c26, some c1827, some c126, some c541, some c1828, some c1414, some c239, some c333, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1829 : lratChecker f1829 p1829 = .success := by decide +kernel
theorem unsat1829 : Unsatisfiable (PosFin 57) f1829 := by
  apply lratCheckerSound f1829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1829
  · intro a ha; simp [p1829] at ha; subst a; trivial
  · exact checked1829
theorem derived1829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1829 := by
  apply localUnsat_implies_entails f1829 [c1569, c1785, c112, c1738, c1824, c813, c117, c1822, c267, c17, c26, c1827, c126, c541, c1828, c1414, c239, c333] c1829 unsat1829 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c1824 := derived1824 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c1822 := derived1822 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c1827 := derived1827 a h
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c541 := derived541 a h
  have h14 : Entails.eval a c1828 := derived1828 a h
  have h15 : Entails.eval a c1414 := derived1414 a h
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1830 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c112, some c1738, some c1824, some c813, some c117, some c1822, some c1807, some c1282, some c1829, some c70, some c22, some c1236, some c270, some c228, some c356, some c752, some c1414, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1830 : lratChecker f1830 p1830 = .success := by decide +kernel
theorem unsat1830 : Unsatisfiable (PosFin 57) f1830 := by
  apply lratCheckerSound f1830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1830
  · intro a ha; simp [p1830] at ha; subst a; trivial
  · exact checked1830
theorem derived1830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1830 := by
  apply localUnsat_implies_entails f1830 [c1569, c1785, c112, c1738, c1824, c813, c117, c1822, c1807, c1282, c1829, c70, c22, c1236, c270, c228, c356, c752, c1414] c1830 unsat1830 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c1824 := derived1824 a h
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c1822 := derived1822 a h
  have h8 : Entails.eval a c1807 := derived1807 a h
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c1829 := derived1829 a h
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c1236 := derived1236 a h
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c228 := h 227 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c752 := derived752 a h
  have h18 : Entails.eval a c1414 := derived1414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1831 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1830, some c202, some c1785, some c112, some c1738, some c1824, some c813, some c117, some c1822, some c267, some c26, some c1807, some c1282, some c520, some c169, some c1414, some c205, some c207, some c268, some c1138, some c1423, some c122, some c325, some c84, some c179, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1831 : lratChecker f1831 p1831 = .success := by decide +kernel
theorem unsat1831 : Unsatisfiable (PosFin 57) f1831 := by
  apply lratCheckerSound f1831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1831
  · intro a ha; simp [p1831] at ha; subst a; trivial
  · exact checked1831
theorem derived1831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1831 := by
  apply localUnsat_implies_entails f1831 [c1569, c1733, c1830, c202, c1785, c112, c1738, c1824, c813, c117, c1822, c267, c26, c1807, c1282, c520, c169, c1414, c205, c207, c268, c1138, c1423, c122, c325, c84, c179] c1831 unsat1831 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1830 := derived1830 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1785 := derived1785 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c1824 := derived1824 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c1822 := derived1822 a h
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c1807 := derived1807 a h
  have h14 : Entails.eval a c1282 := derived1282 a h
  have h15 : Entails.eval a c520 := derived520 a h
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c1414 := derived1414 a h
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c207 := h 206 (by decide)
  have h20 : Entails.eval a c268 := h 267 (by decide)
  have h21 : Entails.eval a c1138 := derived1138 a h
  have h22 : Entails.eval a c1423 := derived1423 a h
  have h23 : Entails.eval a c122 := h 121 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  have h25 : Entails.eval a c84 := h 83 (by decide)
  have h26 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1832 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1822, some c1807, some c1282, some c1785, some c112, some c267, some c26, some c1824, some c813, some c1763, some c1830, some c202, some c148, some c1831, some c516, some c22, some c42, some c899, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1832 : lratChecker f1832 p1832 = .success := by decide +kernel
theorem unsat1832 : Unsatisfiable (PosFin 57) f1832 := by
  apply lratCheckerSound f1832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1832
  · intro a ha; simp [p1832] at ha; subst a; trivial
  · exact checked1832
theorem derived1832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1832 := by
  apply localUnsat_implies_entails f1832 [c1733, c1569, c1822, c1807, c1282, c1785, c112, c267, c26, c1824, c813, c1763, c1830, c202, c148, c1831, c516, c22, c42, c899] c1832 unsat1832 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1822 := derived1822 a h
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1785 := derived1785 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1824 := derived1824 a h
  have h10 : Entails.eval a c813 := derived813 a h
  have h11 : Entails.eval a c1763 := derived1763 a h
  have h12 : Entails.eval a c1830 := derived1830 a h
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c148 := h 147 (by decide)
  have h15 : Entails.eval a c1831 := derived1831 a h
  have h16 : Entails.eval a c516 := derived516 a h
  have h17 : Entails.eval a c22 := h 21 (by decide)
  have h18 : Entails.eval a c42 := h 41 (by decide)
  have h19 : Entails.eval a c899 := derived899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1833 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1785, some c1832, some c119, some c1650, some c1822, some c1807, some c1282, some c112, some c266, some c212, some c30, some c1669, some c37, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1833 : lratChecker f1833 p1833 = .success := by decide +kernel
theorem unsat1833 : Unsatisfiable (PosFin 57) f1833 := by
  apply lratCheckerSound f1833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1833
  · intro a ha; simp [p1833] at ha; subst a; trivial
  · exact checked1833
theorem derived1833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1833 := by
  apply localUnsat_implies_entails f1833 [c1569, c1785, c1832, c119, c1650, c1822, c1807, c1282, c112, c266, c212, c30, c1669, c37] c1833 unsat1833 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c1832 := derived1832 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1650 := derived1650 a h
  have h5 : Entails.eval a c1822 := derived1822 a h
  have h6 : Entails.eval a c1807 := derived1807 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c1669 := derived1669 a h
  have h13 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1834 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1832, some c1822, some c1807, some c1282, some c1785, some c112, some c119, some c201, some c203, some c1763, some c1833, some c26, some c17, some c734, some c1669, some c167, some c270, some c899, some c1431, some c359, some c132, some c50, some c232, some c169, some c338, some c261, some c6, some c95, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1834 : lratChecker f1834 p1834 = .success := by decide +kernel
theorem unsat1834 : Unsatisfiable (PosFin 57) f1834 := by
  apply lratCheckerSound f1834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1834
  · intro a ha; simp [p1834] at ha; subst a; trivial
  · exact checked1834
theorem derived1834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1834 := by
  apply localUnsat_implies_entails f1834 [c1733, c1569, c1832, c1822, c1807, c1282, c1785, c112, c119, c201, c203, c1763, c1833, c26, c17, c734, c1669, c167, c270, c899, c1431, c359, c132, c50, c232, c169, c338, c261, c6, c95] c1834 unsat1834 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1832 := derived1832 a h
  have h3 : Entails.eval a c1822 := derived1822 a h
  have h4 : Entails.eval a c1807 := derived1807 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1785 := derived1785 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c1763 := derived1763 a h
  have h12 : Entails.eval a c1833 := derived1833 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c734 := derived734 a h
  have h16 : Entails.eval a c1669 := derived1669 a h
  have h17 : Entails.eval a c167 := h 166 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c899 := derived899 a h
  have h20 : Entails.eval a c1431 := derived1431 a h
  have h21 : Entails.eval a c359 := h 358 (by decide)
  have h22 : Entails.eval a c132 := h 131 (by decide)
  have h23 : Entails.eval a c50 := h 49 (by decide)
  have h24 : Entails.eval a c232 := h 231 (by decide)
  have h25 : Entails.eval a c169 := h 168 (by decide)
  have h26 : Entails.eval a c338 := h 337 (by decide)
  have h27 : Entails.eval a c261 := h 260 (by decide)
  have h28 : Entails.eval a c6 := h 5 (by decide)
  have h29 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1835 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1785, some c1832, some c112, some c1834, some c813, some c1763, some c127, some c90, some c1822, some c1807, some c1282, some c266, some c1436, some c30, some c202, some c1641, some c148, some c212, some c37, some c45, some c252, some c338, some c185, some c369, some c50, some c368, some c299, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1835 : lratChecker f1835 p1835 = .success := by decide +kernel
theorem unsat1835 : Unsatisfiable (PosFin 57) f1835 := by
  apply lratCheckerSound f1835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1835
  · intro a ha; simp [p1835] at ha; subst a; trivial
  · exact checked1835
theorem derived1835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1835 := by
  apply localUnsat_implies_entails f1835 [c1569, c1733, c1785, c1832, c112, c1834, c813, c1763, c127, c90, c1822, c1807, c1282, c266, c1436, c30, c202, c1641, c148, c212, c37, c45, c252, c338, c185, c369, c50, c368, c299] c1835 unsat1835 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1785 := derived1785 a h
  have h3 : Entails.eval a c1832 := derived1832 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1834 := derived1834 a h
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c90 := h 89 (by decide)
  have h10 : Entails.eval a c1822 := derived1822 a h
  have h11 : Entails.eval a c1807 := derived1807 a h
  have h12 : Entails.eval a c1282 := derived1282 a h
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c1436 := derived1436 a h
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c202 := h 201 (by decide)
  have h17 : Entails.eval a c1641 := derived1641 a h
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c212 := h 211 (by decide)
  have h20 : Entails.eval a c37 := h 36 (by decide)
  have h21 : Entails.eval a c45 := h 44 (by decide)
  have h22 : Entails.eval a c252 := h 251 (by decide)
  have h23 : Entails.eval a c338 := h 337 (by decide)
  have h24 : Entails.eval a c185 := h 184 (by decide)
  have h25 : Entails.eval a c369 := h 368 (by decide)
  have h26 : Entails.eval a c50 := h 49 (by decide)
  have h27 : Entails.eval a c368 := h 367 (by decide)
  have h28 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1836 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1832, some c1785, some c112, some c1834, some c813, some c1763, some c127, some c1835, some c17, some c323, some c26, some c90, some c1822, some c1807, some c1282, some c202, some c140, some c270, some c133, some c515, some c237, some c8, some c357, some c327, some c1199, some c44, some c182, some c12, some c223, some c1414, some c144, some c58, some c217, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1836 : lratChecker f1836 p1836 = .success := by decide +kernel
theorem unsat1836 : Unsatisfiable (PosFin 57) f1836 := by
  apply lratCheckerSound f1836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1836
  · intro a ha; simp [p1836] at ha; subst a; trivial
  · exact checked1836
theorem derived1836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1836 := by
  apply localUnsat_implies_entails f1836 [c1733, c1569, c1832, c1785, c112, c1834, c813, c1763, c127, c1835, c17, c323, c26, c90, c1822, c1807, c1282, c202, c140, c270, c133, c515, c237, c8, c357, c327, c1199, c44, c182, c12, c223, c1414, c144, c58, c217] c1836 unsat1836 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1832 := derived1832 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1834 := derived1834 a h
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c1835 := derived1835 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c1822 := derived1822 a h
  have h15 : Entails.eval a c1807 := derived1807 a h
  have h16 : Entails.eval a c1282 := derived1282 a h
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c140 := h 139 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c515 := derived515 a h
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c8 := h 7 (by decide)
  have h24 : Entails.eval a c357 := h 356 (by decide)
  have h25 : Entails.eval a c327 := h 326 (by decide)
  have h26 : Entails.eval a c1199 := derived1199 a h
  have h27 : Entails.eval a c44 := h 43 (by decide)
  have h28 : Entails.eval a c182 := h 181 (by decide)
  have h29 : Entails.eval a c12 := h 11 (by decide)
  have h30 : Entails.eval a c223 := h 222 (by decide)
  have h31 : Entails.eval a c1414 := derived1414 a h
  have h32 : Entails.eval a c144 := h 143 (by decide)
  have h33 : Entails.eval a c58 := h 57 (by decide)
  have h34 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1837 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1832, some c1822, some c1785, some c112, some c1834, some c813, some c1763, some c127, some c1835, some c26, some c1836, some c148, some c171, some c516, some c520, some c169, some c92, some c207, some c413, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1837 : lratChecker f1837 p1837 = .success := by decide +kernel
theorem unsat1837 : Unsatisfiable (PosFin 57) f1837 := by
  apply lratCheckerSound f1837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1837
  · intro a ha; simp [p1837] at ha; subst a; trivial
  · exact checked1837
theorem derived1837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1837 := by
  apply localUnsat_implies_entails f1837 [c1569, c1832, c1822, c1785, c112, c1834, c813, c1763, c127, c1835, c26, c1836, c148, c171, c516, c520, c169, c92, c207, c413] c1837 unsat1837 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1832 := derived1832 a h
  have h2 : Entails.eval a c1822 := derived1822 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1834 := derived1834 a h
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c1835 := derived1835 a h
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c1836 := derived1836 a h
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c516 := derived516 a h
  have h15 : Entails.eval a c520 := derived520 a h
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c92 := h 91 (by decide)
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c413 := derived413 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1838 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1822, some c1807, some c1282, some c1785, some c1832, some c1837, some c22, some c42, some c270, some c223, some c899, some c44, some c1650, some c8, some c133, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1838 : lratChecker f1838 p1838 = .success := by decide +kernel
theorem unsat1838 : Unsatisfiable (PosFin 57) f1838 := by
  apply lratCheckerSound f1838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1838
  · intro a ha; simp [p1838] at ha; subst a; trivial
  · exact checked1838
theorem derived1838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1838 := by
  apply localUnsat_implies_entails f1838 [c1822, c1807, c1282, c1785, c1832, c1837, c22, c42, c270, c223, c899, c44, c1650, c8, c133] c1838 unsat1838 (by rfl) a
  have h0 : Entails.eval a c1822 := derived1822 a h
  have h1 : Entails.eval a c1807 := derived1807 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c1832 := derived1832 a h
  have h5 : Entails.eval a c1837 := derived1837 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c223 := h 222 (by decide)
  have h10 : Entails.eval a c899 := derived899 a h
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c1650 := derived1650 a h
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1839 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨30, by decide⟩, false), (⟨35, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c359, some c26, some c1673, some c172, some c792, some c839, some c207, some c669, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1839 : lratChecker f1839 p1839 = .success := by decide +kernel
theorem unsat1839 : Unsatisfiable (PosFin 57) f1839 := by
  apply lratCheckerSound f1839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1839
  · intro a ha; simp [p1839] at ha; subst a; trivial
  · exact checked1839
theorem derived1839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1839 := by
  apply localUnsat_implies_entails f1839 [c1569, c359, c26, c1673, c172, c792, c839, c207, c669] c1839 unsat1839 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c1673 := derived1673 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c792 := derived792 a h
  have h6 : Entails.eval a c839 := derived839 a h
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c669 := derived669 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1840 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1822, some c1807, some c1282, some c1838, some c267, some c17, some c354, some c22, some c270, some c42, some c1785, some c112, some c70, some c355, some c1791, some c26, some c1738, some c1839, some c201, some c125, some c734, some c132, some c532, some c330, some c1124, some c237, some c179, some c328, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1840 : lratChecker f1840 p1840 = .success := by decide +kernel
theorem unsat1840 : Unsatisfiable (PosFin 57) f1840 := by
  apply lratCheckerSound f1840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1840
  · intro a ha; simp [p1840] at ha; subst a; trivial
  · exact checked1840
theorem derived1840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1840 := by
  apply localUnsat_implies_entails f1840 [c1569, c1733, c1822, c1807, c1282, c1838, c267, c17, c354, c22, c270, c42, c1785, c112, c70, c355, c1791, c26, c1738, c1839, c201, c125, c734, c132, c532, c330, c1124, c237, c179, c328] c1840 unsat1840 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1822 := derived1822 a h
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1838 := derived1838 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c354 := h 353 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c1785 := derived1785 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c1791 := derived1791 a h
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c1738 := derived1738 a h
  have h19 : Entails.eval a c1839 := derived1839 a h
  have h20 : Entails.eval a c201 := h 200 (by decide)
  have h21 : Entails.eval a c125 := h 124 (by decide)
  have h22 : Entails.eval a c734 := derived734 a h
  have h23 : Entails.eval a c132 := h 131 (by decide)
  have h24 : Entails.eval a c532 := derived532 a h
  have h25 : Entails.eval a c330 := h 329 (by decide)
  have h26 : Entails.eval a c1124 := derived1124 a h
  have h27 : Entails.eval a c237 := h 236 (by decide)
  have h28 : Entails.eval a c179 := h 178 (by decide)
  have h29 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1841 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1838, some c1822, some c1807, some c1282, some c1785, some c112, some c267, some c1738, some c17, some c355, some c354, some c70, some c22, some c270, some c1840, some c117, some c228, some c201, some c804, some c356, some c168, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1841 : lratChecker f1841 p1841 = .success := by decide +kernel
theorem unsat1841 : Unsatisfiable (PosFin 57) f1841 := by
  apply lratCheckerSound f1841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1841
  · intro a ha; simp [p1841] at ha; subst a; trivial
  · exact checked1841
theorem derived1841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1841 := by
  apply localUnsat_implies_entails f1841 [c1569, c1733, c1838, c1822, c1807, c1282, c1785, c112, c267, c1738, c17, c355, c354, c70, c22, c270, c1840, c117, c228, c201, c804, c356, c168] c1841 unsat1841 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1838 := derived1838 a h
  have h3 : Entails.eval a c1822 := derived1822 a h
  have h4 : Entails.eval a c1807 := derived1807 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1785 := derived1785 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c1738 := derived1738 a h
  have h10 : Entails.eval a c17 := h 16 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c270 := h 269 (by decide)
  have h16 : Entails.eval a c1840 := derived1840 a h
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  have h20 : Entails.eval a c804 := derived804 a h
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1842 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1807, some c1282, some c1785, some c112, some c1822, some c1838, some c354, some c17, some c266, some c30, some c66, some c358, some c1841, some c813, some c359, some c229, some c232, some c268, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1842 : lratChecker f1842 p1842 = .success := by decide +kernel
theorem unsat1842 : Unsatisfiable (PosFin 57) f1842 := by
  apply lratCheckerSound f1842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1842
  · intro a ha; simp [p1842] at ha; subst a; trivial
  · exact checked1842
theorem derived1842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1842 := by
  apply localUnsat_implies_entails f1842 [c1569, c1807, c1282, c1785, c112, c1822, c1838, c354, c17, c266, c30, c66, c358, c1841, c813, c359, c229, c232, c268] c1842 unsat1842 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1807 := derived1807 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c1822 := derived1822 a h
  have h6 : Entails.eval a c1838 := derived1838 a h
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c1841 := derived1841 a h
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c232 := h 231 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1843 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1733, some c1841, some c1838, some c1822, some c1807, some c1282, some c1785, some c112, some c354, some c358, some c17, some c66, some c266, some c30, some c1842, some c1138, some c1641, some c201, some c119, some c127, some c1436, some c136, some c336, some c331, some c202, some c1139, some c179, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1843 : lratChecker f1843 p1843 = .success := by decide +kernel
theorem unsat1843 : Unsatisfiable (PosFin 57) f1843 := by
  apply lratCheckerSound f1843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1843
  · intro a ha; simp [p1843] at ha; subst a; trivial
  · exact checked1843
theorem derived1843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1843 := by
  apply localUnsat_implies_entails f1843 [c1569, c1733, c1841, c1838, c1822, c1807, c1282, c1785, c112, c354, c358, c17, c66, c266, c30, c1842, c1138, c1641, c201, c119, c127, c1436, c136, c336, c331, c202, c1139, c179] c1843 unsat1843 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1841 := derived1841 a h
  have h3 : Entails.eval a c1838 := derived1838 a h
  have h4 : Entails.eval a c1822 := derived1822 a h
  have h5 : Entails.eval a c1807 := derived1807 a h
  have h6 : Entails.eval a c1282 := derived1282 a h
  have h7 : Entails.eval a c1785 := derived1785 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c1842 := derived1842 a h
  have h16 : Entails.eval a c1138 := derived1138 a h
  have h17 : Entails.eval a c1641 := derived1641 a h
  have h18 : Entails.eval a c201 := h 200 (by decide)
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c127 := h 126 (by decide)
  have h21 : Entails.eval a c1436 := derived1436 a h
  have h22 : Entails.eval a c136 := h 135 (by decide)
  have h23 : Entails.eval a c336 := h 335 (by decide)
  have h24 : Entails.eval a c331 := h 330 (by decide)
  have h25 : Entails.eval a c202 := h 201 (by decide)
  have h26 : Entails.eval a c1139 := derived1139 a h
  have h27 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1844 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c112, some c1807, some c1282, some c1822, some c1838, some c1841, some c1843, some c70, some c22, some c42, some c1820, some c270, some c266, some c223, some c355, some c26, some c119, some c1791, some c229, some c201, some c356, some c159, some c734, some c712, some c155, some c320, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1844 : lratChecker f1844 p1844 = .success := by decide +kernel
theorem unsat1844 : Unsatisfiable (PosFin 57) f1844 := by
  apply lratCheckerSound f1844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1844
  · intro a ha; simp [p1844] at ha; subst a; trivial
  · exact checked1844
theorem derived1844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1844 := by
  apply localUnsat_implies_entails f1844 [c1733, c1569, c112, c1807, c1282, c1822, c1838, c1841, c1843, c70, c22, c42, c1820, c270, c266, c223, c355, c26, c119, c1791, c229, c201, c356, c159, c734, c712, c155, c320] c1844 unsat1844 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1822 := derived1822 a h
  have h6 : Entails.eval a c1838 := derived1838 a h
  have h7 : Entails.eval a c1841 := derived1841 a h
  have h8 : Entails.eval a c1843 := derived1843 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c1820 := derived1820 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c223 := h 222 (by decide)
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c1791 := derived1791 a h
  have h20 : Entails.eval a c229 := h 228 (by decide)
  have h21 : Entails.eval a c201 := h 200 (by decide)
  have h22 : Entails.eval a c356 := h 355 (by decide)
  have h23 : Entails.eval a c159 := h 158 (by decide)
  have h24 : Entails.eval a c734 := derived734 a h
  have h25 : Entails.eval a c712 := derived712 a h
  have h26 : Entails.eval a c155 := h 154 (by decide)
  have h27 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1845 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1785, some c1844, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1845 : lratChecker f1845 p1845 = .success := by decide +kernel
theorem unsat1845 : Unsatisfiable (PosFin 57) f1845 := by
  apply lratCheckerSound f1845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1845
  · intro a ha; simp [p1845] at ha; subst a; trivial
  · exact checked1845
theorem derived1845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1845 := by
  apply localUnsat_implies_entails f1845 [c1785, c1844] c1845 unsat1845 (by rfl) a
  have h0 : Entails.eval a c1785 := derived1785 a h
  have h1 : Entails.eval a c1844 := derived1844 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1846 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1738, some c21, some c813, some c203, some c147, some c1786, some c211, some c1282, some c37, some c45, some c338, some c337, some c102, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1846 : lratChecker f1846 p1846 = .success := by decide +kernel
theorem unsat1846 : Unsatisfiable (PosFin 57) f1846 := by
  apply lratCheckerSound f1846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1846
  · intro a ha; simp [p1846] at ha; subst a; trivial
  · exact checked1846
theorem derived1846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1846 := by
  apply localUnsat_implies_entails f1846 [c1733, c1569, c1845, c1738, c21, c813, c203, c147, c1786, c211, c1282, c37, c45, c338, c337, c102] c1846 unsat1846 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c1786 := derived1786 a h
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c1282 := derived1282 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c338 := h 337 (by decide)
  have h14 : Entails.eval a c337 := h 336 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1847 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1738, some c21, some c813, some c203, some c147, some c1846, some c26, some c1673, some c39, some c47, some c54, some c346, some c313, some c49, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1847 : lratChecker f1847 p1847 = .success := by decide +kernel
theorem unsat1847 : Unsatisfiable (PosFin 57) f1847 := by
  apply lratCheckerSound f1847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1847
  · intro a ha; simp [p1847] at ha; subst a; trivial
  · exact checked1847
theorem derived1847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1847 := by
  apply localUnsat_implies_entails f1847 [c1733, c1569, c1845, c1738, c21, c813, c203, c147, c1846, c26, c1673, c39, c47, c54, c346, c313, c49] c1847 unsat1847 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c1846 := derived1846 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1673 := derived1673 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c54 := h 53 (by decide)
  have h14 : Entails.eval a c346 := h 345 (by decide)
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1848 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c34, some c899, some c62, some c58, some c319, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1848 : lratChecker f1848 p1848 = .success := by decide +kernel
theorem unsat1848 : Unsatisfiable (PosFin 57) f1848 := by
  apply lratCheckerSound f1848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1848
  · intro a ha; simp [p1848] at ha; subst a; trivial
  · exact checked1848
theorem derived1848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1848 := by
  apply localUnsat_implies_entails f1848 [c1845, c34, c899, c62, c58, c319] c1848 unsat1848 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c899 := derived899 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1849 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1569, some c1738, some c21, some c813, some c1847, some c120, some c685, some c267, some c147, some c26, some c17, some c201, some c734, some c167, some c359, some c169, some c280, some c1848, some c1282, some c28, some c1681, some c270, some c27, some c715, some c13, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1849 : lratChecker f1849 p1849 = .success := by decide +kernel
theorem unsat1849 : Unsatisfiable (PosFin 57) f1849 := by
  apply lratCheckerSound f1849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1849
  · intro a ha; simp [p1849] at ha; subst a; trivial
  · exact checked1849
theorem derived1849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1849 := by
  apply localUnsat_implies_entails f1849 [c1733, c1845, c1569, c1738, c21, c813, c1847, c120, c685, c267, c147, c26, c17, c201, c734, c167, c359, c169, c280, c1848, c1282, c28, c1681, c270, c27, c715, c13] c1849 unsat1849 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c813 := derived813 a h
  have h6 : Entails.eval a c1847 := derived1847 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c685 := derived685 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c734 := derived734 a h
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c1848 := derived1848 a h
  have h20 : Entails.eval a c1282 := derived1282 a h
  have h21 : Entails.eval a c28 := h 27 (by decide)
  have h22 : Entails.eval a c1681 := derived1681 a h
  have h23 : Entails.eval a c270 := h 269 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  have h25 : Entails.eval a c715 := derived715 a h
  have h26 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1850 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨31, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c797, some c1849, some c1077, some c357, some c233, some c24, some c265, some c211, some c37, some c45, some c338, some c337, some c102, some c1282, some c1597, some c28, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1850 : lratChecker f1850 p1850 = .success := by decide +kernel
theorem unsat1850 : Unsatisfiable (PosFin 57) f1850 := by
  apply lratCheckerSound f1850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1850
  · intro a ha; simp [p1850] at ha; subst a; trivial
  · exact checked1850
theorem derived1850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1850 := by
  apply localUnsat_implies_entails f1850 [c1569, c1845, c797, c1849, c1077, c357, c233, c24, c265, c211, c37, c45, c338, c337, c102, c1282, c1597, c28] c1850 unsat1850 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c797 := derived797 a h
  have h3 : Entails.eval a c1849 := derived1849 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c338 := h 337 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c1597 := derived1597 a h
  have h17 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1851 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c25, some c1425, some c8, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1851 : lratChecker f1851 p1851 = .success := by decide +kernel
theorem unsat1851 : Unsatisfiable (PosFin 57) f1851 := by
  apply lratCheckerSound f1851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1851
  · intro a ha; simp [p1851] at ha; subst a; trivial
  · exact checked1851
theorem derived1851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1851 := by
  apply localUnsat_implies_entails f1851 [c1569, c25, c1425, c8] c1851 unsat1851 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c1425 := derived1425 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1852 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c120, some c202, some c233, some c24, some c231, some c1851, some c269, some c134, some c207, some c741, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1852 : lratChecker f1852 p1852 = .success := by decide +kernel
theorem unsat1852 : Unsatisfiable (PosFin 57) f1852 := by
  apply lratCheckerSound f1852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1852
  · intro a ha; simp [p1852] at ha; subst a; trivial
  · exact checked1852
theorem derived1852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1852 := by
  apply localUnsat_implies_entails f1852 [c1733, c120, c202, c233, c24, c231, c1851, c269, c134, c207, c741] c1852 unsat1852 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c1851 := derived1851 a h
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c741 := derived741 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1853 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1849, some c1077, some c357, some c24, some c120, some c233, some c202, some c203, some c147, some c168, some c1850, some c1852, some c272, some c1681, some c268, some c108, some c8, some c122, some c727, some c1684, some c81, some c327, some c178, some c1225, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1853 : lratChecker f1853 p1853 = .success := by decide +kernel
theorem unsat1853 : Unsatisfiable (PosFin 57) f1853 := by
  apply lratCheckerSound f1853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1853
  · intro a ha; simp [p1853] at ha; subst a; trivial
  · exact checked1853
theorem derived1853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1853 := by
  apply localUnsat_implies_entails f1853 [c1733, c1845, c1849, c1077, c357, c24, c120, c233, c202, c203, c147, c168, c1850, c1852, c272, c1681, c268, c108, c8, c122, c727, c1684, c81, c327, c178, c1225] c1853 unsat1853 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1849 := derived1849 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c1850 := derived1850 a h
  have h13 : Entails.eval a c1852 := derived1852 a h
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c1681 := derived1681 a h
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c108 := h 107 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c122 := h 121 (by decide)
  have h20 : Entails.eval a c727 := derived727 a h
  have h21 : Entails.eval a c1684 := derived1684 a h
  have h22 : Entails.eval a c81 := h 80 (by decide)
  have h23 : Entails.eval a c327 := h 326 (by decide)
  have h24 : Entails.eval a c178 := h 177 (by decide)
  have h25 : Entails.eval a c1225 := derived1225 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1854 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c202, some c123, some c134, some c325, some c270, some c25, some c122, some c8, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1854 : lratChecker f1854 p1854 = .success := by decide +kernel
theorem unsat1854 : Unsatisfiable (PosFin 57) f1854 := by
  apply lratCheckerSound f1854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1854
  · intro a ha; simp [p1854] at ha; subst a; trivial
  · exact checked1854
theorem derived1854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1854 := by
  apply localUnsat_implies_entails f1854 [c1733, c1569, c202, c123, c134, c325, c270, c25, c122, c8] c1854 unsat1854 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1855 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨32, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c202, some c9, some c207, some c204, some c27, some c741, some c744, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1855 : lratChecker f1855 p1855 = .success := by decide +kernel
theorem unsat1855 : Unsatisfiable (PosFin 57) f1855 := by
  apply lratCheckerSound f1855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1855
  · intro a ha; simp [p1855] at ha; subst a; trivial
  · exact checked1855
theorem derived1855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1855 := by
  apply localUnsat_implies_entails f1855 [c1733, c1569, c202, c9, c207, c204, c27, c741, c744] c1855 unsat1855 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c741 := derived741 a h
  have h8 : Entails.eval a c744 := derived744 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1856 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1855, some c115, some c1854, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1856 : lratChecker f1856 p1856 = .success := by decide +kernel
theorem unsat1856 : Unsatisfiable (PosFin 57) f1856 := by
  apply lratCheckerSound f1856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1856
  · intro a ha; simp [p1856] at ha; subst a; trivial
  · exact checked1856
theorem derived1856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1856 := by
  apply localUnsat_implies_entails f1856 [c1077, c1855, c115, c1854] c1856 unsat1856 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1855 := derived1855 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1854 := derived1854 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1857 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c270, some c221, some c25, some c27, some c108, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1857 : lratChecker f1857 p1857 = .success := by decide +kernel
theorem unsat1857 : Unsatisfiable (PosFin 57) f1857 := by
  apply lratCheckerSound f1857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1857
  · intro a ha; simp [p1857] at ha; subst a; trivial
  · exact checked1857
theorem derived1857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1857 := by
  apply localUnsat_implies_entails f1857 [c1569, c270, c221, c25, c27, c108] c1857 unsat1857 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c221 := h 220 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1858 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c17, some c1857, some c34, some c126, some c541, some c1282, some c297, some c1681, some c239, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1858 : lratChecker f1858 p1858 = .success := by decide +kernel
theorem unsat1858 : Unsatisfiable (PosFin 57) f1858 := by
  apply lratCheckerSound f1858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1858
  · intro a ha; simp [p1858] at ha; subst a; trivial
  · exact checked1858
theorem derived1858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1858 := by
  apply localUnsat_implies_entails f1858 [c1569, c1845, c17, c1857, c34, c126, c541, c1282, c297, c1681, c239] c1858 unsat1858 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c1857 := derived1857 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c541 := derived541 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c1681 := derived1681 a h
  have h10 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1859 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1853, some c267, some c1849, some c1077, some c357, some c202, some c203, some c147, some c168, some c224, some c44, some c281, some c1856, some c272, some c1673, some c1858, some c154, some c207, some c734, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1859 : lratChecker f1859 p1859 = .success := by decide +kernel
theorem unsat1859 : Unsatisfiable (PosFin 57) f1859 := by
  apply lratCheckerSound f1859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1859
  · intro a ha; simp [p1859] at ha; subst a; trivial
  · exact checked1859
theorem derived1859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1859 := by
  apply localUnsat_implies_entails f1859 [c1733, c1853, c267, c1849, c1077, c357, c202, c203, c147, c168, c224, c44, c281, c1856, c272, c1673, c1858, c154, c207, c734] c1859 unsat1859 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1853 := derived1853 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c1849 := derived1849 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c281 := h 280 (by decide)
  have h13 : Entails.eval a c1856 := derived1856 a h
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c1673 := derived1673 a h
  have h16 : Entails.eval a c1858 := derived1858 a h
  have h17 : Entails.eval a c154 := h 153 (by decide)
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c734 := derived734 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1860 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, true), (⟨35, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c17, some c123, some c325, some c330, some c176, some c205, some c134, some c182, some c270, some c322, some c237, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1860 : lratChecker f1860 p1860 = .success := by decide +kernel
theorem unsat1860 : Unsatisfiable (PosFin 57) f1860 := by
  apply lratCheckerSound f1860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1860
  · intro a ha; simp [p1860] at ha; subst a; trivial
  · exact checked1860
theorem derived1860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1860 := by
  apply localUnsat_implies_entails f1860 [c1569, c17, c123, c325, c330, c176, c205, c134, c182, c270, c322, c237] c1860 unsat1860 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c330 := h 329 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1861 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1077, some c25, some c237, some c108, some c84, some c1199, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1861 : lratChecker f1861 p1861 = .success := by decide +kernel
theorem unsat1861 : Unsatisfiable (PosFin 57) f1861 := by
  apply lratCheckerSound f1861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1861
  · intro a ha; simp [p1861] at ha; subst a; trivial
  · exact checked1861
theorem derived1861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1861 := by
  apply localUnsat_implies_entails f1861 [c1569, c1077, c25, c237, c108, c84, c1199] c1861 unsat1861 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c1199 := derived1199 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1862 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1569, some c1849, some c1077, some c357, some c1853, some c267, some c17, some c1859, some c148, some c685, some c169, some c704, some c147, some c167, some c201, some c1763, some c1860, some c272, some c125, some c532, some c330, some c179, some c1861, some c270, some c268, some c34, some c715, some c27, some c13, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1862 : lratChecker f1862 p1862 = .success := by decide +kernel
theorem unsat1862 : Unsatisfiable (PosFin 57) f1862 := by
  apply lratCheckerSound f1862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1862
  · intro a ha; simp [p1862] at ha; subst a; trivial
  · exact checked1862
theorem derived1862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1862 := by
  apply localUnsat_implies_entails f1862 [c1733, c1845, c1569, c1849, c1077, c357, c1853, c267, c17, c1859, c148, c685, c169, c704, c147, c167, c201, c1763, c1860, c272, c125, c532, c330, c179, c1861, c270, c268, c34, c715, c27, c13] c1862 unsat1862 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1849 := derived1849 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c1853 := derived1853 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c1859 := derived1859 a h
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c685 := derived685 a h
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c704 := derived704 a h
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c1763 := derived1763 a h
  have h18 : Entails.eval a c1860 := derived1860 a h
  have h19 : Entails.eval a c272 := h 271 (by decide)
  have h20 : Entails.eval a c125 := h 124 (by decide)
  have h21 : Entails.eval a c532 := derived532 a h
  have h22 : Entails.eval a c330 := h 329 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  have h24 : Entails.eval a c1861 := derived1861 a h
  have h25 : Entails.eval a c270 := h 269 (by decide)
  have h26 : Entails.eval a c268 := h 267 (by decide)
  have h27 : Entails.eval a c34 := h 33 (by decide)
  have h28 : Entails.eval a c715 := derived715 a h
  have h29 : Entails.eval a c27 := h 26 (by decide)
  have h30 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1863 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c120, some c202, some c1077, some c360, some c353, some c231, some c1768, some c1681, some c108, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1863 : lratChecker f1863 p1863 = .success := by decide +kernel
theorem unsat1863 : Unsatisfiable (PosFin 57) f1863 := by
  apply lratCheckerSound f1863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1863
  · intro a ha; simp [p1863] at ha; subst a; trivial
  · exact checked1863
theorem derived1863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1863 := by
  apply localUnsat_implies_entails f1863 [c1733, c1845, c120, c202, c1077, c360, c353, c231, c1768, c1681, c108] c1863 unsat1863 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c1768 := derived1768 a h
  have h9 : Entails.eval a c1681 := derived1681 a h
  have h10 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1864 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1862, some c1849, some c1077, some c357, some c120, some c233, some c203, some c1863, some c235, some c797, some c1092, some c1316, some c272, some c156, some c1852, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1864 : lratChecker f1864 p1864 = .success := by decide +kernel
theorem unsat1864 : Unsatisfiable (PosFin 57) f1864 := by
  apply lratCheckerSound f1864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1864
  · intro a ha; simp [p1864] at ha; subst a; trivial
  · exact checked1864
theorem derived1864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1864 := by
  apply localUnsat_implies_entails f1864 [c1733, c1845, c1862, c1849, c1077, c357, c120, c233, c203, c1863, c235, c797, c1092, c1316, c272, c156, c1852] c1864 unsat1864 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1862 := derived1862 a h
  have h3 : Entails.eval a c1849 := derived1849 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c1863 := derived1863 a h
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c797 := derived797 a h
  have h12 : Entails.eval a c1092 := derived1092 a h
  have h13 : Entails.eval a c1316 := derived1316 a h
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c156 := h 155 (by decide)
  have h16 : Entails.eval a c1852 := derived1852 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1865 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c207, some c1014, some c116, some c220, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1865 : lratChecker f1865 p1865 = .success := by decide +kernel
theorem unsat1865 : Unsatisfiable (PosFin 57) f1865 := by
  apply lratCheckerSound f1865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1865
  · intro a ha; simp [p1865] at ha; subst a; trivial
  · exact checked1865
theorem derived1865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1865 := by
  apply localUnsat_implies_entails f1865 [c207, c1014, c116, c220] c1865 unsat1865 (by rfl) a
  have h0 : Entails.eval a c207 := h 206 (by decide)
  have h1 : Entails.eval a c1014 := derived1014 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1866 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c1854, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1866 : lratChecker f1866 p1866 = .success := by decide +kernel
theorem unsat1866 : Unsatisfiable (PosFin 57) f1866 := by
  apply lratCheckerSound f1866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1866
  · intro a ha; simp [p1866] at ha; subst a; trivial
  · exact checked1866
theorem derived1866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1866 := by
  apply localUnsat_implies_entails f1866 [c115, c1854] c1866 unsat1866 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c1854 := derived1854 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1867 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨37, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c41, some c21, some c1077, some c1866, some c1014, some c1865, some c220, some c737, some c116, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1867 : lratChecker f1867 p1867 = .success := by decide +kernel
theorem unsat1867 : Unsatisfiable (PosFin 57) f1867 := by
  apply lratCheckerSound f1867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1867
  · intro a ha; simp [p1867] at ha; subst a; trivial
  · exact checked1867
theorem derived1867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1867 := by
  apply localUnsat_implies_entails f1867 [c1845, c41, c21, c1077, c1866, c1014, c1865, c220, c737, c116] c1867 unsat1867 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1866 := derived1866 a h
  have h5 : Entails.eval a c1014 := derived1014 a h
  have h6 : Entails.eval a c1865 := derived1865 a h
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c737 := derived737 a h
  have h9 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1868 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c1849, some c1077, some c357, some c1862, some c1864, some c267, some c17, some c353, some c797, some c21, some c41, some c75, some c1763, some c272, some c1867, some c169, some c171, some c1865, some c167, some c123, some c331, some c325, some c177, some c205, some c160, some c134, some c899, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1868 : lratChecker f1868 p1868 = .success := by decide +kernel
theorem unsat1868 : Unsatisfiable (PosFin 57) f1868 := by
  apply lratCheckerSound f1868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1868
  · intro a ha; simp [p1868] at ha; subst a; trivial
  · exact checked1868
theorem derived1868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1868 := by
  apply localUnsat_implies_entails f1868 [c1845, c1569, c1849, c1077, c357, c1862, c1864, c267, c17, c353, c797, c21, c41, c75, c1763, c272, c1867, c169, c171, c1865, c167, c123, c331, c325, c177, c205, c160, c134, c899] c1868 unsat1868 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1849 := derived1849 a h
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c1862 := derived1862 a h
  have h6 : Entails.eval a c1864 := derived1864 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c797 := derived797 a h
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c1763 := derived1763 a h
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c1867 := derived1867 a h
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c171 := h 170 (by decide)
  have h19 : Entails.eval a c1865 := derived1865 a h
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c123 := h 122 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c325 := h 324 (by decide)
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c205 := h 204 (by decide)
  have h26 : Entails.eval a c160 := h 159 (by decide)
  have h27 : Entails.eval a c134 := h 133 (by decide)
  have h28 : Entails.eval a c899 := derived899 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1869 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c1738, some c813, some c21, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1869 : lratChecker f1869 p1869 = .success := by decide +kernel
theorem unsat1869 : Unsatisfiable (PosFin 57) f1869 := by
  apply lratCheckerSound f1869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1869
  · intro a ha; simp [p1869] at ha; subst a; trivial
  · exact checked1869
theorem derived1869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1869 := by
  apply localUnsat_implies_entails f1869 [c1569, c1845, c1738, c813, c21] c1869 unsat1869 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1870 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1868, some c202, some c146, some c118, some c1791, some c1092, some c210, some c353, some c37, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1870 : lratChecker f1870 p1870 = .success := by decide +kernel
theorem unsat1870 : Unsatisfiable (PosFin 57) f1870 := by
  apply lratCheckerSound f1870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1870
  · intro a ha; simp [p1870] at ha; subst a; trivial
  · exact checked1870
theorem derived1870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1870 := by
  apply localUnsat_implies_entails f1870 [c1733, c1569, c1868, c202, c146, c118, c1791, c1092, c210, c353, c37] c1870 unsat1870 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1868 := derived1868 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c1092 := derived1092 a h
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1871 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1569, some c1868, some c120, some c202, some c1791, some c118, some c1869, some c1077, some c1870, some c17, some c353, some c235, some c74, some c272, some c1282, some c231, some c25, some c356, some c269, some c233, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1871 : lratChecker f1871 p1871 = .success := by decide +kernel
theorem unsat1871 : Unsatisfiable (PosFin 57) f1871 := by
  apply lratCheckerSound f1871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1871
  · intro a ha; simp [p1871] at ha; subst a; trivial
  · exact checked1871
theorem derived1871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1871 := by
  apply localUnsat_implies_entails f1871 [c1733, c1845, c1569, c1868, c120, c202, c1791, c118, c1869, c1077, c1870, c17, c353, c235, c74, c272, c1282, c231, c25, c356, c269, c233] c1871 unsat1871 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c1868 := derived1868 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c1869 := derived1869 a h
  have h9 : Entails.eval a c1077 := derived1077 a h
  have h10 : Entails.eval a c1870 := derived1870 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c1282 := derived1282 a h
  have h17 : Entails.eval a c231 := h 230 (by decide)
  have h18 : Entails.eval a c25 := h 24 (by decide)
  have h19 : Entails.eval a c356 := h 355 (by decide)
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1872 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨24, by decide⟩, false), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1845, some c1569, some c17, some c202, some c1791, some c118, some c353, some c270, some c74, some c25, some c1282, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p1872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1872 : lratChecker f1872 p1872 = .success := by decide +kernel
theorem unsat1872 : Unsatisfiable (PosFin 57) f1872 := by
  apply lratCheckerSound f1872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1872
  · intro a ha; simp [p1872] at ha; subst a; trivial
  · exact checked1872
theorem derived1872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1872 := by
  apply localUnsat_implies_entails f1872 [c1733, c1845, c1569, c17, c202, c1791, c118, c353, c270, c74, c25, c1282] c1872 unsat1872 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1569 := derived1569 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c1791 := derived1791 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1873 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1868, some c1871, some c267, some c1872, some c685, some c148, some c1278, some c284, some c899, some c318, some c22, some c53, some c1282, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1873 : lratChecker f1873 p1873 = .success := by decide +kernel
theorem unsat1873 : Unsatisfiable (PosFin 57) f1873 := by
  apply lratCheckerSound f1873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1873
  · intro a ha; simp [p1873] at ha; subst a; trivial
  · exact checked1873
theorem derived1873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1873 := by
  apply localUnsat_implies_entails f1873 [c1569, c1868, c1871, c267, c1872, c685, c148, c1278, c284, c899, c318, c22, c53, c1282] c1873 unsat1873 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1868 := derived1868 a h
  have h2 : Entails.eval a c1871 := derived1871 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c1872 := derived1872 a h
  have h5 : Entails.eval a c685 := derived685 a h
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c1278 := derived1278 a h
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c899 := derived899 a h
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c1282 := derived1282 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1874 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1845, some c1868, some c1871, some c267, some c17, some c1872, some c148, some c685, some c1236, some c1873, some c1869, some c353, some c1077, some c74, some c21, some c1763, some c1282, some c272, some c25, some c270, some c216, some c612, some c153, some c169, some c205, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1874 : lratChecker f1874 p1874 = .success := by decide +kernel
theorem unsat1874 : Unsatisfiable (PosFin 57) f1874 := by
  apply lratCheckerSound f1874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1874
  · intro a ha; simp [p1874] at ha; subst a; trivial
  · exact checked1874
theorem derived1874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1874 := by
  apply localUnsat_implies_entails f1874 [c1569, c1845, c1868, c1871, c267, c17, c1872, c148, c685, c1236, c1873, c1869, c353, c1077, c74, c21, c1763, c1282, c272, c25, c270, c216, c612, c153, c169, c205] c1874 unsat1874 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1868 := derived1868 a h
  have h3 : Entails.eval a c1871 := derived1871 a h
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c1872 := derived1872 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c685 := derived685 a h
  have h9 : Entails.eval a c1236 := derived1236 a h
  have h10 : Entails.eval a c1873 := derived1873 a h
  have h11 : Entails.eval a c1869 := derived1869 a h
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c1077 := derived1077 a h
  have h14 : Entails.eval a c74 := h 73 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c1763 := derived1763 a h
  have h17 : Entails.eval a c1282 := derived1282 a h
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c25 := h 24 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  have h22 : Entails.eval a c612 := derived612 a h
  have h23 : Entails.eval a c153 := h 152 (by decide)
  have h24 : Entails.eval a c169 := h 168 (by decide)
  have h25 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1875 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c24, some c1874, some c127, some c119, some c813, some c235, some c1049, some c41, some c1491, some c45, some c54, some c339, some c320, some c218, some c51, some c1787, some c92, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1875 : lratChecker f1875 p1875 = .success := by decide +kernel
theorem unsat1875 : Unsatisfiable (PosFin 57) f1875 := by
  apply lratCheckerSound f1875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1875
  · intro a ha; simp [p1875] at ha; subst a; trivial
  · exact checked1875
theorem derived1875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1875 := by
  apply localUnsat_implies_entails f1875 [c1845, c1569, c24, c1874, c127, c119, c813, c235, c1049, c41, c1491, c45, c54, c339, c320, c218, c51, c1787, c92] c1875 unsat1875 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c1874 := derived1874 a h
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c235 := h 234 (by decide)
  have h8 : Entails.eval a c1049 := derived1049 a h
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c1491 := derived1491 a h
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c339 := h 338 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c51 := h 50 (by decide)
  have h17 : Entails.eval a c1787 := derived1787 a h
  have h18 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1876 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1874, some c127, some c119, some c1077, some c357, some c233, some c1863, some c1316, some c235, some c1014, some c271, some c115, some c123, some c331, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1876 : lratChecker f1876 p1876 = .success := by decide +kernel
theorem unsat1876 : Unsatisfiable (PosFin 57) f1876 := by
  apply lratCheckerSound f1876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1876
  · intro a ha; simp [p1876] at ha; subst a; trivial
  · exact checked1876
theorem derived1876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1876 := by
  apply localUnsat_implies_entails f1876 [c1845, c1874, c127, c119, c1077, c357, c233, c1863, c1316, c235, c1014, c271, c115, c123, c331] c1876 unsat1876 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1874 := derived1874 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c1863 := derived1863 a h
  have h8 : Entails.eval a c1316 := derived1316 a h
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c1014 := derived1014 a h
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1877 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1874, some c202, some c203, some c140, some c119, some c1876, some c813, some c1875, some c235, some c41, some c26, some c271, some c218, some c233, some c39, some c357, some c1748, some c68, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1877 : lratChecker f1877 p1877 = .success := by decide +kernel
theorem unsat1877 : Unsatisfiable (PosFin 57) f1877 := by
  apply lratCheckerSound f1877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1877
  · intro a ha; simp [p1877] at ha; subst a; trivial
  · exact checked1877
theorem derived1877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1877 := by
  apply localUnsat_implies_entails f1877 [c1733, c1569, c1845, c1874, c202, c203, c140, c119, c1876, c813, c1875, c235, c41, c26, c271, c218, c233, c39, c357, c1748, c68] c1877 unsat1877 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1874 := derived1874 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c1876 := derived1876 a h
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c1875 := derived1875 a h
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c233 := h 232 (by decide)
  have h17 : Entails.eval a c39 := h 38 (by decide)
  have h18 : Entails.eval a c357 := h 356 (by decide)
  have h19 : Entails.eval a c1748 := derived1748 a h
  have h20 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1878 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1874, some c202, some c203, some c119, some c140, some c1877, some c1436, some c270, some c17, some c25, some c133, some c353, some c8, some c75, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1878 : lratChecker f1878 p1878 = .success := by decide +kernel
theorem unsat1878 : Unsatisfiable (PosFin 57) f1878 := by
  apply lratCheckerSound f1878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1878
  · intro a ha; simp [p1878] at ha; subst a; trivial
  · exact checked1878
theorem derived1878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1878 := by
  apply localUnsat_implies_entails f1878 [c1733, c1569, c1845, c1874, c202, c203, c119, c140, c1877, c1436, c270, c17, c25, c133, c353, c8, c75] c1878 unsat1878 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1874 := derived1874 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c1877 := derived1877 a h
  have h9 : Entails.eval a c1436 := derived1436 a h
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1879 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1845, some c1874, some c119, some c1763, some c23, some c1878, some c148, some c120, some c212, some c37, some c45, some c252, some c187, some c338, some c337, some c103, some c102, some c49, some c1282, some c1799, some c53, some c96, some c1077, some c1689, some c318, some c341, some c312, some c306, some c320, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1879 : lratChecker f1879 p1879 = .success := by decide +kernel
theorem unsat1879 : Unsatisfiable (PosFin 57) f1879 := by
  apply lratCheckerSound f1879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1879
  · intro a ha; simp [p1879] at ha; subst a; trivial
  · exact checked1879
theorem derived1879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1879 := by
  apply localUnsat_implies_entails f1879 [c1733, c1569, c1845, c1874, c119, c1763, c23, c1878, c148, c120, c212, c37, c45, c252, c187, c338, c337, c103, c102, c49, c1282, c1799, c53, c96, c1077, c1689, c318, c341, c312, c306, c320] c1879 unsat1879 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c1874 := derived1874 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c1763 := derived1763 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c1878 := derived1878 a h
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c102 := h 101 (by decide)
  have h19 : Entails.eval a c49 := h 48 (by decide)
  have h20 : Entails.eval a c1282 := derived1282 a h
  have h21 : Entails.eval a c1799 := derived1799 a h
  have h22 : Entails.eval a c53 := h 52 (by decide)
  have h23 : Entails.eval a c96 := h 95 (by decide)
  have h24 : Entails.eval a c1077 := derived1077 a h
  have h25 : Entails.eval a c1689 := derived1689 a h
  have h26 : Entails.eval a c318 := h 317 (by decide)
  have h27 : Entails.eval a c341 := h 340 (by decide)
  have h28 : Entails.eval a c312 := h 311 (by decide)
  have h29 : Entails.eval a c306 := h 305 (by decide)
  have h30 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1880 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1879, some c17, some c1874, some c119, some c1763, some c201, some c1878, some c734, some c167, some c359, some c1431, some c232, some c169, some c125, some c532, some c268, some c638, some c330, some c237, some c229, some c205, some c178, some c327, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1880 : lratChecker f1880 p1880 = .success := by decide +kernel
theorem unsat1880 : Unsatisfiable (PosFin 57) f1880 := by
  apply lratCheckerSound f1880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1880
  · intro a ha; simp [p1880] at ha; subst a; trivial
  · exact checked1880
theorem derived1880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1880 := by
  apply localUnsat_implies_entails f1880 [c1733, c1569, c1879, c17, c1874, c119, c1763, c201, c1878, c734, c167, c359, c1431, c232, c169, c125, c532, c268, c638, c330, c237, c229, c205, c178, c327] c1880 unsat1880 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1879 := derived1879 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c1874 := derived1874 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c1763 := derived1763 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c1878 := derived1878 a h
  have h9 : Entails.eval a c734 := derived734 a h
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c1431 := derived1431 a h
  have h13 : Entails.eval a c232 := h 231 (by decide)
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c532 := derived532 a h
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c638 := derived638 a h
  have h19 : Entails.eval a c330 := h 329 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c229 := h 228 (by decide)
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c178 := h 177 (by decide)
  have h24 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1881 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1733, some c1569, some c1878, some c148, some c120, some c1874, some c119, some c201, some c1763, some c1879, some c1880, some c26, some c1077, some c704, some c357, some c167, some c169, some c1860, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1881 : lratChecker f1881 p1881 = .success := by decide +kernel
theorem unsat1881 : Unsatisfiable (PosFin 57) f1881 := by
  apply lratCheckerSound f1881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1881
  · intro a ha; simp [p1881] at ha; subst a; trivial
  · exact checked1881
theorem derived1881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1881 := by
  apply localUnsat_implies_entails f1881 [c1733, c1569, c1878, c148, c120, c1874, c119, c201, c1763, c1879, c1880, c26, c1077, c704, c357, c167, c169, c1860] c1881 unsat1881 (by rfl) a
  have h0 : Entails.eval a c1733 := derived1733 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1878 := derived1878 a h
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c1874 := derived1874 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c1763 := derived1763 a h
  have h9 : Entails.eval a c1879 := derived1879 a h
  have h10 : Entails.eval a c1880 := derived1880 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c1077 := derived1077 a h
  have h13 : Entails.eval a c704 := derived704 a h
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c1860 := derived1860 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1882 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c1881, some c1878, some c148, some c120, some c212, some c37, some c45, some c353, some c338, some c21, some c1763, some c249, some c102, some c1282, some c68, some c53, some c357, some c216, some c1638, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1882 : lratChecker f1882 p1882 = .success := by decide +kernel
theorem unsat1882 : Unsatisfiable (PosFin 57) f1882 := by
  apply lratCheckerSound f1882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1882
  · intro a ha; simp [p1882] at ha; subst a; trivial
  · exact checked1882
theorem derived1882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1882 := by
  apply localUnsat_implies_entails f1882 [c1845, c1569, c1881, c1878, c148, c120, c212, c37, c45, c353, c338, c21, c1763, c249, c102, c1282, c68, c53, c357, c216, c1638] c1882 unsat1882 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1881 := derived1881 a h
  have h3 : Entails.eval a c1878 := derived1878 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c338 := h 337 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c1763 := derived1763 a h
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c68 := h 67 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  have h18 : Entails.eval a c357 := h 356 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c1638 := derived1638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1883 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1845, some c1569, some c1874, some c1881, some c1882, some c17, some c353, some c1763, some c127, some c1878, some c171, some c75, some c41, some c21, some c26, some c271, some c218, some c136, some c39, some c54, some c207, some c1759, some c313, some c413, some c51, some c92, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1883 : lratChecker f1883 p1883 = .success := by decide +kernel
theorem unsat1883 : Unsatisfiable (PosFin 57) f1883 := by
  apply lratCheckerSound f1883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1883
  · intro a ha; simp [p1883] at ha; subst a; trivial
  · exact checked1883
theorem derived1883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1883 := by
  apply localUnsat_implies_entails f1883 [c1845, c1569, c1874, c1881, c1882, c17, c353, c1763, c127, c1878, c171, c75, c41, c21, c26, c271, c218, c136, c39, c54, c207, c1759, c313, c413, c51, c92] c1883 unsat1883 (by rfl) a
  have h0 : Entails.eval a c1845 := derived1845 a h
  have h1 : Entails.eval a c1569 := derived1569 a h
  have h2 : Entails.eval a c1874 := derived1874 a h
  have h3 : Entails.eval a c1881 := derived1881 a h
  have h4 : Entails.eval a c1882 := derived1882 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c1878 := derived1878 a h
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c218 := h 217 (by decide)
  have h17 : Entails.eval a c136 := h 135 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c207 := h 206 (by decide)
  have h21 : Entails.eval a c1759 := derived1759 a h
  have h22 : Entails.eval a c313 := h 312 (by decide)
  have h23 : Entails.eval a c413 := derived413 a h
  have h24 : Entails.eval a c51 := h 50 (by decide)
  have h25 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1883

end CochromaticTwenty.Certificates.B16_4_2
