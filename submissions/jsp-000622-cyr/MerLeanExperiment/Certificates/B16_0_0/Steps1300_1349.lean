import MerLeanExperiment.Certificates.B16_0_0.Steps1200_1299

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1694 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1677, some c1685, some c108, some c1692, some c1074, some c1158, some c1231, some c246, some c262, some c220, some c348, some c249, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c1564, c1677, c1685, c108, c1692, c1074, c1158, c1231, c246, c262, c220, c348, c249] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1677 := derived1677 a h
  have h2 : Entails.eval a c1685 := derived1685 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1692 := derived1692 a h
  have h5 : Entails.eval a c1074 := derived1074 a h
  have h6 : Entails.eval a c1158 := derived1158 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c348 := h 347 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1677, some c1685, some c108, some c1231, some c1692, some c246, some c1690, some c109, some c1074, some c1158, some c1694, some c843, some c346, some c247, some c1693, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1564, c1677, c1685, c108, c1231, c1692, c246, c1690, c109, c1074, c1158, c1694, c843, c346, c247, c1693] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1677 := derived1677 a h
  have h2 : Entails.eval a c1685 := derived1685 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c1692 := derived1692 a h
  have h6 : Entails.eval a c246 := h 245 (by decide)
  have h7 : Entails.eval a c1690 := derived1690 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c1074 := derived1074 a h
  have h10 : Entails.eval a c1158 := derived1158 a h
  have h11 : Entails.eval a c1694 := derived1694 a h
  have h12 : Entails.eval a c843 := derived843 a h
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c1693 := derived1693 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1635, some c1671, some c1677, some c1685, some c108, some c1230, some c1231, some c1690, some c109, some c1692, some c262, some c246, some c1695, some c1182, some c360, some c64, some c151, some c354, some c114, some c346, some c44, some c45, some c181, some c144, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1564, c1635, c1671, c1677, c1685, c108, c1230, c1231, c1690, c109, c1692, c262, c246, c1695, c1182, c360, c64, c151, c354, c114, c346, c44, c45, c181, c144] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1677 := derived1677 a h
  have h4 : Entails.eval a c1685 := derived1685 a h
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c1230 := derived1230 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c1690 := derived1690 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c1692 := derived1692 a h
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c1695 := derived1695 a h
  have h14 : Entails.eval a c1182 := derived1182 a h
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c64 := h 63 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c114 := h 113 (by decide)
  have h20 : Entails.eval a c346 := h 345 (by decide)
  have h21 : Entails.eval a c44 := h 43 (by decide)
  have h22 : Entails.eval a c45 := h 44 (by decide)
  have h23 : Entails.eval a c181 := h 180 (by decide)
  have h24 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c20, some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c1696, c1564, c20] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c1, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c1696, c1564, c1] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1698, some c1696, some c1564, some c1697, some c21, some c3, some c125, some c1330, some c153, some c112, some c221, some c1187, some c355, some c111, some c66, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1635, c1698, c1696, c1564, c1697, c21, c3, c125, c1330, c153, c112, c221, c1187, c355, c111, c66] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1698 := derived1698 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1697 := derived1697 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c1330 := derived1330 a h
  have h9 : Entails.eval a c153 := h 152 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c1187 := derived1187 a h
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1698, some c1564, some c57, some c67, some c155, some c357, some c12, some c66, some c179, some c111, some c1231, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c1697, c1698, c1564, c57, c67, c155, c357, c12, c66, c179, c111, c1231] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1698 := derived1698 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  have h11 : Entails.eval a c1231 := derived1231 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1696, some c3, some c1700, some c21, some c1699, some c112, some c268, some c28, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1635, c1564, c1696, c3, c1700, c21, c1699, c112, c268, c28] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1700 := derived1700 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c1699 := derived1699 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1698, some c23, some c4, some c153, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c1697, c1698, c23, c4, c153] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1698 := derived1698 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1697, some c1698, some c3, some c57, some c21, some c1701, some c1702, some c251, some c59, some c1232, some c153, some c111, some c427, some c66, some c154, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1635, c1697, c1698, c3, c57, c21, c1701, c1702, c251, c59, c1232, c153, c111, c427, c66, c154] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c1701 := derived1701 a h
  have h7 : Entails.eval a c1702 := derived1702 a h
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c1232 := derived1232 a h
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c427 := derived427 a h
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c1635, some c1698, some c1697, some c1703, some c1141, some c3, some c108, some c28, some c1187, some c114, some c197, some c125, some c271, some c220, some c127, some c155, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c1696, c1564, c1635, c1698, c1697, c1703, c1141, c3, c108, c28, c1187, c114, c197, c125, c271, c220, c127, c155] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c1698 := derived1698 a h
  have h4 : Entails.eval a c1697 := derived1697 a h
  have h5 : Entails.eval a c1703 := derived1703 a h
  have h6 : Entails.eval a c1141 := derived1141 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c1187 := derived1187 a h
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c127 := h 126 (by decide)
  have h17 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1697, some c1698, some c1635, some c3, some c115, some c1703, some c108, some c1231, some c1704, some c109, some c1232, some c387, some c385, some c1233, some c345, some c1208, some c356, some c155, some c357, some c182, some c71, some c48, some c597, some c137, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c1564, c1697, c1698, c1635, c3, c115, c1703, c108, c1231, c1704, c109, c1232, c387, c385, c1233, c345, c1208, c356, c155, c357, c182, c71, c48, c597, c137] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c1703 := derived1703 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c1704 := derived1704 a h
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c1232 := derived1232 a h
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c385 := h 384 (by decide)
  have h14 : Entails.eval a c1233 := derived1233 a h
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c1208 := derived1208 a h
  have h17 : Entails.eval a c356 := h 355 (by decide)
  have h18 : Entails.eval a c155 := h 154 (by decide)
  have h19 : Entails.eval a c357 := h 356 (by decide)
  have h20 : Entails.eval a c182 := h 181 (by decide)
  have h21 : Entails.eval a c71 := h 70 (by decide)
  have h22 : Entails.eval a c48 := h 47 (by decide)
  have h23 : Entails.eval a c597 := derived597 a h
  have h24 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1697, some c1698, some c67, some c1700, some c155, some c15, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c1635, c1697, c1698, c67, c1700, c155, c15] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1700 := derived1700 a h
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c1697, some c1698, some c1705, some c21, some c267, some c29, some c57, some c28, some c252, some c92, some c1289, some c179, some c111, some c66, some c11, some c154, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c1696, c1564, c1697, c1698, c1705, c21, c267, c29, c57, c28, c252, c92, c1289, c179, c111, c66, c11, c154] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c1698 := derived1698 a h
  have h4 : Entails.eval a c1705 := derived1705 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c1289 := derived1289 a h
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1696, some c1635, some c1697, some c1698, some c1705, some c57, some c21, some c1310, some c267, some c29, some c1706, some c1707, some c112, some c1702, some c251, some c59, some c96, some c153, some c111, some c427, some c66, some c154, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c1564, c1696, c1635, c1697, c1698, c1705, c57, c21, c1310, c267, c29, c1706, c1707, c112, c1702, c251, c59, c96, c153, c111, c427, c66, c154] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c1697 := derived1697 a h
  have h4 : Entails.eval a c1698 := derived1698 a h
  have h5 : Entails.eval a c1705 := derived1705 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c1310 := derived1310 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c1706 := derived1706 a h
  have h12 : Entails.eval a c1707 := derived1707 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c1702 := derived1702 a h
  have h15 : Entails.eval a c251 := h 250 (by decide)
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c427 := derived427 a h
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨36, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1696, some c1697, some c1635, some c1708, some c109, some c1187, some c108, some c1604, some c28, some c268, some c224, some c1705, some c267, some c225, some c14, some c1306, some c252, some c192, some c258, some c344, some c15, some c131, some c254, some c165, some c58, some c73, some c1252, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c1564, c1696, c1697, c1635, c1708, c109, c1187, c108, c1604, c28, c268, c224, c1705, c267, c225, c14, c1306, c252, c192, c258, c344, c15, c131, c254, c165, c58, c73, c1252] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1708 := derived1708 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c1187 := derived1187 a h
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c1604 := derived1604 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c1705 := derived1705 a h
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c1306 := derived1306 a h
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c192 := h 191 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c344 := h 343 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c131 := h 130 (by decide)
  have h23 : Entails.eval a c254 := h 253 (by decide)
  have h24 : Entails.eval a c165 := h 164 (by decide)
  have h25 : Entails.eval a c58 := h 57 (by decide)
  have h26 : Entails.eval a c73 := h 72 (by decide)
  have h27 : Entails.eval a c1252 := derived1252 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1564, some c1604, some c1306, some c92, some c1289, some c388, some c344, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c1697, c1564, c1604, c1306, c92, c1289, c388, c344] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1604 := derived1604 a h
  have h3 : Entails.eval a c1306 := derived1306 a h
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c1289 := derived1289 a h
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c1635, some c1698, some c1697, some c1708, some c109, some c28, some c1187, some c268, some c108, some c1306, some c14, some c1710, some c192, some c258, some c1709, some c15, some c119, some c153, some c51, some c116, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c1696, c1564, c1635, c1698, c1697, c1708, c109, c28, c1187, c268, c108, c1306, c14, c1710, c192, c258, c1709, c15, c119, c153, c51, c116] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c1698 := derived1698 a h
  have h4 : Entails.eval a c1697 := derived1697 a h
  have h5 : Entails.eval a c1708 := derived1708 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c1187 := derived1187 a h
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c1306 := derived1306 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c1710 := derived1710 a h
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c1709 := derived1709 a h
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c1564, some c1697, some c1635, some c1711, some c1708, some c109, some c28, some c1705, some c1306, some c1604, some c14, some c1710, some c219, some c192, some c258, some c270, some c1251, some c124, some c1255, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1696, c1564, c1697, c1635, c1711, c1708, c109, c28, c1705, c1306, c1604, c14, c1710, c219, c192, c258, c270, c1251, c124, c1255] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1711 := derived1711 a h
  have h5 : Entails.eval a c1708 := derived1708 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c1705 := derived1705 a h
  have h9 : Entails.eval a c1306 := derived1306 a h
  have h10 : Entails.eval a c1604 := derived1604 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c1710 := derived1710 a h
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c192 := h 191 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c1251 := derived1251 a h
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c1255 := derived1255 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1713 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1696, some c1564, some c1314, some c275, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1713 : lratChecker f1713 p1713 = .success := by decide +kernel
theorem unsat1713 : Unsatisfiable (PosFin 57) f1713 := by
  apply lratCheckerSound f1713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1713
  · intro a ha; simp [p1713] at ha; subst a; trivial
  · exact checked1713
theorem derived1713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1713 := by
  apply localUnsat_implies_entails f1713 [c1697, c1696, c1564, c1314, c275] c1713 unsat1713 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1314 := derived1314 a h
  have h4 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1714 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1696, some c1698, some c1697, some c1708, some c1705, some c109, some c1711, some c1712, some c108, some c29, some c270, some c219, some c154, some c357, some c6, some c118, some c1713, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c1564, c1696, c1698, c1697, c1708, c1705, c109, c1711, c1712, c108, c29, c270, c219, c154, c357, c6, c118, c1713] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c1697 := derived1697 a h
  have h4 : Entails.eval a c1708 := derived1708 a h
  have h5 : Entails.eval a c1705 := derived1705 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1711 := derived1711 a h
  have h8 : Entails.eval a c1712 := derived1712 a h
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c154 := h 153 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c1713 := derived1713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1564, some c1696, some c1697, some c1714, some c1705, some c1231, some c29, some c1232, some c267, some c270, some c387, some c385, some c219, some c345, some c357, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c1564, c1696, c1697, c1714, c1705, c1231, c29, c1232, c267, c270, c387, c385, c219, c345, c357] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c1564 := derived1564 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c1714 := derived1714 a h
  have h4 : Entails.eval a c1705 := derived1705 a h
  have h5 : Entails.eval a c1231 := derived1231 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c1232 := derived1232 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c385 := h 384 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1564, some c1696, some c1698, some c1697, some c1708, some c1714, some c1715, some c108, some c110, some c13, some c1710, some c28, some c153, some c1006, some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c1635, c1564, c1696, c1698, c1697, c1708, c1714, c1715, c108, c110, c13, c1710, c28, c153, c1006] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1698 := derived1698 a h
  have h4 : Entails.eval a c1697 := derived1697 a h
  have h5 : Entails.eval a c1708 := derived1708 a h
  have h6 : Entails.eval a c1714 := derived1714 a h
  have h7 : Entails.eval a c1715 := derived1715 a h
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1710 := derived1710 a h
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c1006 := derived1006 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1716, some c1697, some c1698, some c151, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c1716, c1697, c1698, c151] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c1716 := derived1716 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1716, some c1697, some c353, some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c1716, c1697, c353] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c1716 := derived1716 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1719 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1716, some c1697, some c354, some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p1719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1719 : lratChecker f1719 p1719 = .success := by decide +kernel
theorem unsat1719 : Unsatisfiable (PosFin 57) f1719 := by
  apply lratCheckerSound f1719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1719
  · intro a ha; simp [p1719] at ha; subst a; trivial
  · exact checked1719
theorem derived1719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1719 := by
  apply localUnsat_implies_entails f1719 [c1716, c1697, c354] c1719 unsat1719 (by rfl) a
  have h0 : Entails.eval a c1716 := derived1716 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1720 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1635, some c1719, some c1564, some c1718, some c1716, some c1717, some c1698, some c1696, some c2, some c3, some c221, some c268, some c28, some c222, some c112, some c360, some c12, some c1230, some c1345, some c111, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1720 : lratChecker f1720 p1720 = .success := by decide +kernel
theorem unsat1720 : Unsatisfiable (PosFin 57) f1720 := by
  apply lratCheckerSound f1720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1720
  · intro a ha; simp [p1720] at ha; subst a; trivial
  · exact checked1720
theorem derived1720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1720 := by
  apply localUnsat_implies_entails f1720 [c1635, c1719, c1564, c1718, c1716, c1717, c1698, c1696, c2, c3, c221, c268, c28, c222, c112, c360, c12, c1230, c1345, c111] c1720 unsat1720 (by rfl) a
  have h0 : Entails.eval a c1635 := derived1635 a h
  have h1 : Entails.eval a c1719 := derived1719 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1718 := derived1718 a h
  have h4 : Entails.eval a c1716 := derived1716 a h
  have h5 : Entails.eval a c1717 := derived1717 a h
  have h6 : Entails.eval a c1698 := derived1698 a h
  have h7 : Entails.eval a c1696 := derived1696 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c360 := h 359 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c1230 := derived1230 a h
  have h18 : Entails.eval a c1345 := derived1345 a h
  have h19 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1721 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1698, some c1697, some c1717, some c1718, some c12, some c200, some c155, some c11, some c70, some c111, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1721 : lratChecker f1721 p1721 = .success := by decide +kernel
theorem unsat1721 : Unsatisfiable (PosFin 57) f1721 := by
  apply lratCheckerSound f1721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1721
  · intro a ha; simp [p1721] at ha; subst a; trivial
  · exact checked1721
theorem derived1721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1721 := by
  apply localUnsat_implies_entails f1721 [c1698, c1697, c1717, c1718, c12, c200, c155, c11, c70, c111] c1721 unsat1721 (by rfl) a
  have h0 : Entails.eval a c1698 := derived1698 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1717 := derived1717 a h
  have h3 : Entails.eval a c1718 := derived1718 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1722 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1718, some c1696, some c1564, some c1719, some c1717, some c1716, some c1697, some c1698, some c2, some c1720, some c267, some c29, some c1721, some c112, some c28, some c1209, some c268, some c111, some c225, some c11, some c360, some c154, some c73, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1722 : lratChecker f1722 p1722 = .success := by decide +kernel
theorem unsat1722 : Unsatisfiable (PosFin 57) f1722 := by
  apply lratCheckerSound f1722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1722
  · intro a ha; simp [p1722] at ha; subst a; trivial
  · exact checked1722
theorem derived1722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1722 := by
  apply localUnsat_implies_entails f1722 [c1718, c1696, c1564, c1719, c1717, c1716, c1697, c1698, c2, c1720, c267, c29, c1721, c112, c28, c1209, c268, c111, c225, c11, c360, c154, c73] c1722 unsat1722 (by rfl) a
  have h0 : Entails.eval a c1718 := derived1718 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1719 := derived1719 a h
  have h4 : Entails.eval a c1717 := derived1717 a h
  have h5 : Entails.eval a c1716 := derived1716 a h
  have h6 : Entails.eval a c1697 := derived1697 a h
  have h7 : Entails.eval a c1698 := derived1698 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1720 := derived1720 a h
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c1721 := derived1721 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c1209 := derived1209 a h
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c360 := h 359 (by decide)
  have h21 : Entails.eval a c154 := h 153 (by decide)
  have h22 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1723 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1698, some c1697, some c1717, some c1696, some c1407, some c11, some c154, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1723 : lratChecker f1723 p1723 = .success := by decide +kernel
theorem unsat1723 : Unsatisfiable (PosFin 57) f1723 := by
  apply lratCheckerSound f1723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1723
  · intro a ha; simp [p1723] at ha; subst a; trivial
  · exact checked1723
theorem derived1723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1723 := by
  apply localUnsat_implies_entails f1723 [c1698, c1697, c1717, c1696, c1407, c11, c154] c1723 unsat1723 (by rfl) a
  have h0 : Entails.eval a c1698 := derived1698 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1717 := derived1717 a h
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1407 := derived1407 a h
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1724 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1717, some c1719, some c1564, some c1696, some c1716, some c1718, some c2, some c1722, some c1702, some c68, some c268, some c1723, some c111, some c29, some c1144, some c267, some c222, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1724 : lratChecker f1724 p1724 = .success := by decide +kernel
theorem unsat1724 : Unsatisfiable (PosFin 57) f1724 := by
  apply lratCheckerSound f1724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1724
  · intro a ha; simp [p1724] at ha; subst a; trivial
  · exact checked1724
theorem derived1724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1724 := by
  apply localUnsat_implies_entails f1724 [c1717, c1719, c1564, c1696, c1716, c1718, c2, c1722, c1702, c68, c268, c1723, c111, c29, c1144, c267, c222] c1724 unsat1724 (by rfl) a
  have h0 : Entails.eval a c1717 := derived1717 a h
  have h1 : Entails.eval a c1719 := derived1719 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c1696 := derived1696 a h
  have h4 : Entails.eval a c1716 := derived1716 a h
  have h5 : Entails.eval a c1718 := derived1718 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c1722 := derived1722 a h
  have h8 : Entails.eval a c1702 := derived1702 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1723 := derived1723 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c1144 := derived1144 a h
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1725 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1718, some c1719, some c1724, some c1635, some c1717, some c221, some c1141, some c268, some c114, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1725 : lratChecker f1725 p1725 = .success := by decide +kernel
theorem unsat1725 : Unsatisfiable (PosFin 57) f1725 := by
  apply lratCheckerSound f1725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1725
  · intro a ha; simp [p1725] at ha; subst a; trivial
  · exact checked1725
theorem derived1725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1725 := by
  apply localUnsat_implies_entails f1725 [c1718, c1719, c1724, c1635, c1717, c221, c1141, c268, c114] c1725 unsat1725 (by rfl) a
  have h0 : Entails.eval a c1718 := derived1718 a h
  have h1 : Entails.eval a c1719 := derived1719 a h
  have h2 : Entails.eval a c1724 := derived1724 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1717 := derived1717 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c1141 := derived1141 a h
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1726 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1724, some c1718, some c1696, some c1564, some c1716, some c28, some c1187, some c269, some c108, some c1209, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1726 : lratChecker f1726 p1726 = .success := by decide +kernel
theorem unsat1726 : Unsatisfiable (PosFin 57) f1726 := by
  apply lratCheckerSound f1726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1726
  · intro a ha; simp [p1726] at ha; subst a; trivial
  · exact checked1726
theorem derived1726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1726 := by
  apply localUnsat_implies_entails f1726 [c1724, c1718, c1696, c1564, c1716, c28, c1187, c269, c108, c1209] c1726 unsat1726 (by rfl) a
  have h0 : Entails.eval a c1724 := derived1724 a h
  have h1 : Entails.eval a c1718 := derived1718 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1564 := derived1564 a h
  have h4 : Entails.eval a c1716 := derived1716 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1187 := derived1187 a h
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c1209 := derived1209 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1727 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1635, some c1717, some c1718, some c1719, some c1716, some c1564, some c1698, some c1724, some c109, some c1306, some c1604, some c14, some c1228, some c183, some c192, some c792, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1727 : lratChecker f1727 p1727 = .success := by decide +kernel
theorem unsat1727 : Unsatisfiable (PosFin 57) f1727 := by
  apply lratCheckerSound f1727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1727
  · intro a ha; simp [p1727] at ha; subst a; trivial
  · exact checked1727
theorem derived1727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1727 := by
  apply localUnsat_implies_entails f1727 [c1697, c1635, c1717, c1718, c1719, c1716, c1564, c1698, c1724, c109, c1306, c1604, c14, c1228, c183, c192, c792] c1727 unsat1727 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1717 := derived1717 a h
  have h3 : Entails.eval a c1718 := derived1718 a h
  have h4 : Entails.eval a c1719 := derived1719 a h
  have h5 : Entails.eval a c1716 := derived1716 a h
  have h6 : Entails.eval a c1564 := derived1564 a h
  have h7 : Entails.eval a c1698 := derived1698 a h
  have h8 : Entails.eval a c1724 := derived1724 a h
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c1306 := derived1306 a h
  have h11 : Entails.eval a c1604 := derived1604 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c1228 := derived1228 a h
  have h14 : Entails.eval a c183 := h 182 (by decide)
  have h15 : Entails.eval a c192 := h 191 (by decide)
  have h16 : Entails.eval a c792 := derived792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1728 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1724, some c1564, some c1696, some c1635, some c1717, some c1697, some c1698, some c1719, some c109, some c28, some c1725, some c1726, some c114, some c45, some c1727, some c108, some c44, some c1231, some c29, some c144, some c1559, some c181, some c154, some c182, some c349, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1728 : lratChecker f1728 p1728 = .success := by decide +kernel
theorem unsat1728 : Unsatisfiable (PosFin 57) f1728 := by
  apply lratCheckerSound f1728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1728
  · intro a ha; simp [p1728] at ha; subst a; trivial
  · exact checked1728
theorem derived1728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1728 := by
  apply localUnsat_implies_entails f1728 [c1724, c1564, c1696, c1635, c1717, c1697, c1698, c1719, c109, c28, c1725, c1726, c114, c45, c1727, c108, c44, c1231, c29, c144, c1559, c181, c154, c182, c349] c1728 unsat1728 (by rfl) a
  have h0 : Entails.eval a c1724 := derived1724 a h
  have h1 : Entails.eval a c1564 := derived1564 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1717 := derived1717 a h
  have h5 : Entails.eval a c1697 := derived1697 a h
  have h6 : Entails.eval a c1698 := derived1698 a h
  have h7 : Entails.eval a c1719 := derived1719 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c1725 := derived1725 a h
  have h11 : Entails.eval a c1726 := derived1726 a h
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c1727 := derived1727 a h
  have h15 : Entails.eval a c108 := h 107 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c1231 := derived1231 a h
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c144 := h 143 (by decide)
  have h20 : Entails.eval a c1559 := derived1559 a h
  have h21 : Entails.eval a c181 := h 180 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  have h23 : Entails.eval a c182 := h 181 (by decide)
  have h24 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1729 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1728, some c1702, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1729 : lratChecker f1729 p1729 = .success := by decide +kernel
theorem unsat1729 : Unsatisfiable (PosFin 57) f1729 := by
  apply lratCheckerSound f1729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1729
  · intro a ha; simp [p1729] at ha; subst a; trivial
  · exact checked1729
theorem derived1729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1729 := by
  apply localUnsat_implies_entails f1729 [c1728, c1702] c1729 unsat1729 (by rfl) a
  have h0 : Entails.eval a c1728 := derived1728 a h
  have h1 : Entails.eval a c1702 := derived1702 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1730 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1728, some c1718, some c1719, some c68, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1730 : lratChecker f1730 p1730 = .success := by decide +kernel
theorem unsat1730 : Unsatisfiable (PosFin 57) f1730 := by
  apply lratCheckerSound f1730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1730
  · intro a ha; simp [p1730] at ha; subst a; trivial
  · exact checked1730
theorem derived1730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1730 := by
  apply localUnsat_implies_entails f1730 [c1728, c1718, c1719, c68] c1730 unsat1730 (by rfl) a
  have h0 : Entails.eval a c1728 := derived1728 a h
  have h1 : Entails.eval a c1718 := derived1718 a h
  have h2 : Entails.eval a c1719 := derived1719 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1731 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1730, some c1724, some c108, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1731 : lratChecker f1731 p1731 = .success := by decide +kernel
theorem unsat1731 : Unsatisfiable (PosFin 57) f1731 := by
  apply lratCheckerSound f1731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1731
  · intro a ha; simp [p1731] at ha; subst a; trivial
  · exact checked1731
theorem derived1731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1731 := by
  apply localUnsat_implies_entails f1731 [c1730, c1724, c108] c1731 unsat1731 (by rfl) a
  have h0 : Entails.eval a c1730 := derived1730 a h
  have h1 : Entails.eval a c1724 := derived1724 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1732 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1731, some c1696, some c1564, some c29, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1732 : lratChecker f1732 p1732 = .success := by decide +kernel
theorem unsat1732 : Unsatisfiable (PosFin 57) f1732 := by
  apply lratCheckerSound f1732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1732
  · intro a ha; simp [p1732] at ha; subst a; trivial
  · exact checked1732
theorem derived1732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1732 := by
  apply localUnsat_implies_entails f1732 [c1731, c1696, c1564, c29] c1732 unsat1732 (by rfl) a
  have h0 : Entails.eval a c1731 := derived1731 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1564 := derived1564 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1733 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1731, some c1716, some c1728, some c1144, some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1733 : lratChecker f1733 p1733 = .success := by decide +kernel
theorem unsat1733 : Unsatisfiable (PosFin 57) f1733 := by
  apply lratCheckerSound f1733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1733
  · intro a ha; simp [p1733] at ha; subst a; trivial
  · exact checked1733
theorem derived1733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1733 := by
  apply localUnsat_implies_entails f1733 [c1731, c1716, c1728, c1144] c1733 unsat1733 (by rfl) a
  have h0 : Entails.eval a c1731 := derived1731 a h
  have h1 : Entails.eval a c1716 := derived1716 a h
  have h2 : Entails.eval a c1728 := derived1728 a h
  have h3 : Entails.eval a c1144 := derived1144 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1734 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1729, some c1732, some c1733, some c1718, some c268, some c267, some c222, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1734 : lratChecker f1734 p1734 = .success := by decide +kernel
theorem unsat1734 : Unsatisfiable (PosFin 57) f1734 := by
  apply lratCheckerSound f1734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1734
  · intro a ha; simp [p1734] at ha; subst a; trivial
  · exact checked1734
theorem derived1734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1734 := by
  apply localUnsat_implies_entails f1734 [c1729, c1732, c1733, c1718, c268, c267, c222] c1734 unsat1734 (by rfl) a
  have h0 : Entails.eval a c1729 := derived1729 a h
  have h1 : Entails.eval a c1732 := derived1732 a h
  have h2 : Entails.eval a c1733 := derived1733 a h
  have h3 : Entails.eval a c1718 := derived1718 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1735 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1734, some c1717, some c114, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1735 : lratChecker f1735 p1735 = .success := by decide +kernel
theorem unsat1735 : Unsatisfiable (PosFin 57) f1735 := by
  apply lratCheckerSound f1735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1735
  · intro a ha; simp [p1735] at ha; subst a; trivial
  · exact checked1735
theorem derived1735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1735 := by
  apply localUnsat_implies_entails f1735 [c1734, c1717, c114] c1735 unsat1735 (by rfl) a
  have h0 : Entails.eval a c1734 := derived1734 a h
  have h1 : Entails.eval a c1717 := derived1717 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1736 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1735, some c1635, some c1724, some c1141, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1736 : lratChecker f1736 p1736 = .success := by decide +kernel
theorem unsat1736 : Unsatisfiable (PosFin 57) f1736 := by
  apply lratCheckerSound f1736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1736
  · intro a ha; simp [p1736] at ha; subst a; trivial
  · exact checked1736
theorem derived1736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1736 := by
  apply localUnsat_implies_entails f1736 [c1735, c1635, c1724, c1141] c1736 unsat1736 (by rfl) a
  have h0 : Entails.eval a c1735 := derived1735 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c1724 := derived1724 a h
  have h3 : Entails.eval a c1141 := derived1141 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1737 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1736, some c1732, some c270, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p1737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1737 : lratChecker f1737 p1737 = .success := by decide +kernel
theorem unsat1737 : Unsatisfiable (PosFin 57) f1737 := by
  apply lratCheckerSound f1737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1737
  · intro a ha; simp [p1737] at ha; subst a; trivial
  · exact checked1737
theorem derived1737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1737 := by
  apply localUnsat_implies_entails f1737 [c1736, c1732, c270] c1737 unsat1737 (by rfl) a
  have h0 : Entails.eval a c1736 := derived1736 a h
  have h1 : Entails.eval a c1732 := derived1732 a h
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1738 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1736, some c1732, some c1717, some c1559, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1738 : lratChecker f1738 p1738 = .success := by decide +kernel
theorem unsat1738 : Unsatisfiable (PosFin 57) f1738 := by
  apply lratCheckerSound f1738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1738
  · intro a ha; simp [p1738] at ha; subst a; trivial
  · exact checked1738
theorem derived1738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1738 := by
  apply localUnsat_implies_entails f1738 [c1736, c1732, c1717, c1559] c1738 unsat1738 (by rfl) a
  have h0 : Entails.eval a c1736 := derived1736 a h
  have h1 : Entails.eval a c1732 := derived1732 a h
  have h2 : Entails.eval a c1717 := derived1717 a h
  have h3 : Entails.eval a c1559 := derived1559 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1739 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1698, some c200, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1739 : lratChecker f1739 p1739 = .success := by decide +kernel
theorem unsat1739 : Unsatisfiable (PosFin 57) f1739 := by
  apply lratCheckerSound f1739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1739
  · intro a ha; simp [p1739] at ha; subst a; trivial
  · exact checked1739
theorem derived1739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1739 := by
  apply localUnsat_implies_entails f1739 [c1738, c1698, c200] c1739 unsat1739 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1698 := derived1698 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1740 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1698, some c1697, some c154, some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p1740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1740 : lratChecker f1740 p1740 = .success := by decide +kernel
theorem unsat1740 : Unsatisfiable (PosFin 57) f1740 := by
  apply lratCheckerSound f1740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1740
  · intro a ha; simp [p1740] at ha; subst a; trivial
  · exact checked1740
theorem derived1740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1740 := by
  apply localUnsat_implies_entails f1740 [c1738, c1698, c1697, c154] c1740 unsat1740 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1698 := derived1698 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1741 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1739, some c1732, some c1635, some c1717, some c544, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1741 : lratChecker f1741 p1741 = .success := by decide +kernel
theorem unsat1741 : Unsatisfiable (PosFin 57) f1741 := by
  apply lratCheckerSound f1741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1741
  · intro a ha; simp [p1741] at ha; subst a; trivial
  · exact checked1741
theorem derived1741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1741 := by
  apply localUnsat_implies_entails f1741 [c1739, c1732, c1635, c1717, c544] c1741 unsat1741 (by rfl) a
  have h0 : Entails.eval a c1739 := derived1739 a h
  have h1 : Entails.eval a c1732 := derived1732 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c1717 := derived1717 a h
  have h4 : Entails.eval a c544 := derived544 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1742 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1740, some c1733, some c1737, some c226, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1742 : lratChecker f1742 p1742 = .success := by decide +kernel
theorem unsat1742 : Unsatisfiable (PosFin 57) f1742 := by
  apply lratCheckerSound f1742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1742
  · intro a ha; simp [p1742] at ha; subst a; trivial
  · exact checked1742
theorem derived1742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1742 := by
  apply localUnsat_implies_entails f1742 [c1740, c1733, c1737, c226] c1742 unsat1742 (by rfl) a
  have h0 : Entails.eval a c1740 := derived1740 a h
  have h1 : Entails.eval a c1733 := derived1733 a h
  have h2 : Entails.eval a c1737 := derived1737 a h
  have h3 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1743 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c1742, some c1729, some c271]
def p1743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1743 : lratChecker f1743 p1743 = .success := by decide +kernel
theorem unsat1743 : Unsatisfiable (PosFin 57) f1743 := by
  apply lratCheckerSound f1743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1743
  · intro a ha; simp [p1743] at ha; subst a; trivial
  · exact checked1743
theorem derived1743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1743 := by
  apply localUnsat_implies_entails f1743 [c1741, c1742, c1729, c271] c1743 unsat1743 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c1742 := derived1742 a h
  have h2 : Entails.eval a c1729 := derived1729 a h
  have h3 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1743

end CochromaticTwenty.Certificates.B16_0_0
