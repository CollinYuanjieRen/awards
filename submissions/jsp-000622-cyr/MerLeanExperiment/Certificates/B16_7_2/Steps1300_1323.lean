import MerLeanExperiment.Certificates.B16_7_2.Steps1200_1299

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1689 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c1687, some c1683, some c1677, some c1663, some c1671, some c94, some c82, some c1688, some c313, some c269, some c1638, some c53, some c63, some c52, some c358, some c355, some c87, some c62, some c345, some c1673, some c11, some c5, some c152, some c153, some c166, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1689 : lratChecker f1689 p1689 = .success := by decide +kernel
theorem unsat1689 : Unsatisfiable (PosFin 57) f1689 := by
  apply lratCheckerSound f1689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1689
  · intro a ha; simp [p1689] at ha; subst a; trivial
  · exact checked1689
theorem derived1689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1689 := by
  apply localUnsat_implies_entails f1689 [c1629, c1486, c1643, c1687, c1683, c1677, c1663, c1671, c94, c82, c1688, c313, c269, c1638, c53, c63, c52, c358, c355, c87, c62, c345, c1673, c11, c5, c152, c153, c166] c1689 unsat1689 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c1687 := derived1687 a h
  have h4 : Entails.eval a c1683 := derived1683 a h
  have h5 : Entails.eval a c1677 := derived1677 a h
  have h6 : Entails.eval a c1663 := derived1663 a h
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c1688 := derived1688 a h
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c1638 := derived1638 a h
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c355 := h 354 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c62 := h 61 (by decide)
  have h21 : Entails.eval a c345 := h 344 (by decide)
  have h22 : Entails.eval a c1673 := derived1673 a h
  have h23 : Entails.eval a c11 := h 10 (by decide)
  have h24 : Entails.eval a c5 := h 4 (by decide)
  have h25 : Entails.eval a c152 := h 151 (by decide)
  have h26 : Entails.eval a c153 := h 152 (by decide)
  have h27 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1690 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c1689, some c100, some c1687, some c1683, some c33, some c42, some c278, some c723, some c62, some c333, some c334, some c94, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1690 : lratChecker f1690 p1690 = .success := by decide +kernel
theorem unsat1690 : Unsatisfiable (PosFin 57) f1690 := by
  apply lratCheckerSound f1690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1690
  · intro a ha; simp [p1690] at ha; subst a; trivial
  · exact checked1690
theorem derived1690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1690 := by
  apply localUnsat_implies_entails f1690 [c1643, c1486, c1629, c1689, c100, c1687, c1683, c33, c42, c278, c723, c62, c333, c334, c94] c1690 unsat1690 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c1689 := derived1689 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1687 := derived1687 a h
  have h6 : Entails.eval a c1683 := derived1683 a h
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c723 := derived723 a h
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1691 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c1683, some c1687, some c1689, some c100, some c1690, some c269, some c53, some c62, some c285, some c278, some c82, some c46, some c1638, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1691 : lratChecker f1691 p1691 = .success := by decide +kernel
theorem unsat1691 : Unsatisfiable (PosFin 57) f1691 := by
  apply lratCheckerSound f1691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1691
  · intro a ha; simp [p1691] at ha; subst a; trivial
  · exact checked1691
theorem derived1691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1691 := by
  apply localUnsat_implies_entails f1691 [c1643, c1486, c1629, c1683, c1687, c1689, c100, c1690, c269, c53, c62, c285, c278, c82, c46, c1638] c1691 unsat1691 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c1683 := derived1683 a h
  have h4 : Entails.eval a c1687 := derived1687 a h
  have h5 : Entails.eval a c1689 := derived1689 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c1690 := derived1690 a h
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c1638 := derived1638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1692 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1691, some c908, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1692 : lratChecker f1692 p1692 = .success := by decide +kernel
theorem unsat1692 : Unsatisfiable (PosFin 57) f1692 := by
  apply lratCheckerSound f1692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1692
  · intro a ha; simp [p1692] at ha; subst a; trivial
  · exact checked1692
theorem derived1692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1692 := by
  apply localUnsat_implies_entails f1692 [c1691, c908] c1692 unsat1692 (by rfl) a
  have h0 : Entails.eval a c1691 := derived1691 a h
  have h1 : Entails.eval a c908 := derived908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1693 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1691, some c1051, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1693 : lratChecker f1693 p1693 = .success := by decide +kernel
theorem unsat1693 : Unsatisfiable (PosFin 57) f1693 := by
  apply lratCheckerSound f1693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1693
  · intro a ha; simp [p1693] at ha; subst a; trivial
  · exact checked1693
theorem derived1693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1693 := by
  apply localUnsat_implies_entails f1693 [c1691, c1051] c1693 unsat1693 (by rfl) a
  have h0 : Entails.eval a c1691 := derived1691 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1694 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1691, some c1145, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1694 : lratChecker f1694 p1694 = .success := by decide +kernel
theorem unsat1694 : Unsatisfiable (PosFin 57) f1694 := by
  apply lratCheckerSound f1694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1694
  · intro a ha; simp [p1694] at ha; subst a; trivial
  · exact checked1694
theorem derived1694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1694 := by
  apply localUnsat_implies_entails f1694 [c1691, c1145] c1694 unsat1694 (by rfl) a
  have h0 : Entails.eval a c1691 := derived1691 a h
  have h1 : Entails.eval a c1145 := derived1145 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1695 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1691, some c1444, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1695 : lratChecker f1695 p1695 = .success := by decide +kernel
theorem unsat1695 : Unsatisfiable (PosFin 57) f1695 := by
  apply lratCheckerSound f1695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1695
  · intro a ha; simp [p1695] at ha; subst a; trivial
  · exact checked1695
theorem derived1695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1695 := by
  apply localUnsat_implies_entails f1695 [c1691, c1444] c1695 unsat1695 (by rfl) a
  have h0 : Entails.eval a c1691 := derived1691 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1696 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1691, some c1692, some c1611, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1696 : lratChecker f1696 p1696 = .success := by decide +kernel
theorem unsat1696 : Unsatisfiable (PosFin 57) f1696 := by
  apply lratCheckerSound f1696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1696
  · intro a ha; simp [p1696] at ha; subst a; trivial
  · exact checked1696
theorem derived1696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1696 := by
  apply localUnsat_implies_entails f1696 [c1691, c1692, c1611] c1696 unsat1696 (by rfl) a
  have h0 : Entails.eval a c1691 := derived1691 a h
  have h1 : Entails.eval a c1692 := derived1692 a h
  have h2 : Entails.eval a c1611 := derived1611 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1697 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1693, some c1486, some c1695, some c42, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1697 : lratChecker f1697 p1697 = .success := by decide +kernel
theorem unsat1697 : Unsatisfiable (PosFin 57) f1697 := by
  apply lratCheckerSound f1697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1697
  · intro a ha; simp [p1697] at ha; subst a; trivial
  · exact checked1697
theorem derived1697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1697 := by
  apply localUnsat_implies_entails f1697 [c1693, c1486, c1695, c42] c1697 unsat1697 (by rfl) a
  have h0 : Entails.eval a c1693 := derived1693 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1698 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1693, some c1629, some c1695, some c1697, some c726, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1698 : lratChecker f1698 p1698 = .success := by decide +kernel
theorem unsat1698 : Unsatisfiable (PosFin 57) f1698 := by
  apply lratCheckerSound f1698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1698
  · intro a ha; simp [p1698] at ha; subst a; trivial
  · exact checked1698
theorem derived1698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1698 := by
  apply localUnsat_implies_entails f1698 [c1693, c1629, c1695, c1697, c726] c1698 unsat1698 (by rfl) a
  have h0 : Entails.eval a c1693 := derived1693 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c1697 := derived1697 a h
  have h4 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1699 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1693, some c1629, some c1695, some c46, some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1699 : lratChecker f1699 p1699 = .success := by decide +kernel
theorem unsat1699 : Unsatisfiable (PosFin 57) f1699 := by
  apply lratCheckerSound f1699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1699
  · intro a ha; simp [p1699] at ha; subst a; trivial
  · exact checked1699
theorem derived1699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1699 := by
  apply localUnsat_implies_entails f1699 [c1693, c1629, c1695, c46] c1699 unsat1699 (by rfl) a
  have h0 : Entails.eval a c1693 := derived1693 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1695 := derived1695 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1700 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1697, some c1692, some c1629, some c753, some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p1700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1700 : lratChecker f1700 p1700 = .success := by decide +kernel
theorem unsat1700 : Unsatisfiable (PosFin 57) f1700 := by
  apply lratCheckerSound f1700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1700
  · intro a ha; simp [p1700] at ha; subst a; trivial
  · exact checked1700
theorem derived1700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1700 := by
  apply localUnsat_implies_entails f1700 [c1697, c1692, c1629, c753] c1700 unsat1700 (by rfl) a
  have h0 : Entails.eval a c1697 := derived1697 a h
  have h1 : Entails.eval a c1692 := derived1692 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c753 := derived753 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1701 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1700, some c1694, some c1696, some c211, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1701 : lratChecker f1701 p1701 = .success := by decide +kernel
theorem unsat1701 : Unsatisfiable (PosFin 57) f1701 := by
  apply lratCheckerSound f1701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1701
  · intro a ha; simp [p1701] at ha; subst a; trivial
  · exact checked1701
theorem derived1701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1701 := by
  apply localUnsat_implies_entails f1701 [c1700, c1694, c1696, c211] c1701 unsat1701 (by rfl) a
  have h0 : Entails.eval a c1700 := derived1700 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1696 := derived1696 a h
  have h3 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1702 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1701, some c1643, some c1698, some c24, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1702 : lratChecker f1702 p1702 = .success := by decide +kernel
theorem unsat1702 : Unsatisfiable (PosFin 57) f1702 := by
  apply lratCheckerSound f1702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1702
  · intro a ha; simp [p1702] at ha; subst a; trivial
  · exact checked1702
theorem derived1702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1702 := by
  apply localUnsat_implies_entails f1702 [c1701, c1643, c1698, c24] c1702 unsat1702 (by rfl) a
  have h0 : Entails.eval a c1701 := derived1701 a h
  have h1 : Entails.eval a c1643 := derived1643 a h
  have h2 : Entails.eval a c1698 := derived1698 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1703 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1702, some c1696, some c1694, some c204, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1703 : lratChecker f1703 p1703 = .success := by decide +kernel
theorem unsat1703 : Unsatisfiable (PosFin 57) f1703 := by
  apply lratCheckerSound f1703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1703
  · intro a ha; simp [p1703] at ha; subst a; trivial
  · exact checked1703
theorem derived1703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1703 := by
  apply localUnsat_implies_entails f1703 [c1702, c1696, c1694, c204] c1703 unsat1703 (by rfl) a
  have h0 : Entails.eval a c1702 := derived1702 a h
  have h1 : Entails.eval a c1696 := derived1696 a h
  have h2 : Entails.eval a c1694 := derived1694 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1704 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1694, some c1697, some c1703, some c1699, some c1701, some c1702, some c224, some c275, some c58, some c230, some c286, some c291, some c262, some c233, some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1704 : lratChecker f1704 p1704 = .success := by decide +kernel
theorem unsat1704 : Unsatisfiable (PosFin 57) f1704 := by
  apply lratCheckerSound f1704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1704
  · intro a ha; simp [p1704] at ha; subst a; trivial
  · exact checked1704
theorem derived1704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1704 := by
  apply localUnsat_implies_entails f1704 [c1629, c1694, c1697, c1703, c1699, c1701, c1702, c224, c275, c58, c230, c286, c291, c262, c233] c1704 unsat1704 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1694 := derived1694 a h
  have h2 : Entails.eval a c1697 := derived1697 a h
  have h3 : Entails.eval a c1703 := derived1703 a h
  have h4 : Entails.eval a c1699 := derived1699 a h
  have h5 : Entails.eval a c1701 := derived1701 a h
  have h6 : Entails.eval a c1702 := derived1702 a h
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c275 := h 274 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1705 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1704, some c1695, some c1692, some c1629, some c1360, some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p1705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1705 : lratChecker f1705 p1705 = .success := by decide +kernel
theorem unsat1705 : Unsatisfiable (PosFin 57) f1705 := by
  apply lratCheckerSound f1705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1705
  · intro a ha; simp [p1705] at ha; subst a; trivial
  · exact checked1705
theorem derived1705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1705 := by
  apply localUnsat_implies_entails f1705 [c1704, c1695, c1692, c1629, c1360] c1705 unsat1705 (by rfl) a
  have h0 : Entails.eval a c1704 := derived1704 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1692 := derived1692 a h
  have h3 : Entails.eval a c1629 := derived1629 a h
  have h4 : Entails.eval a c1360 := derived1360 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1706 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1705, some c1699, some c1703, some c275, some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p1706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1706 : lratChecker f1706 p1706 = .success := by decide +kernel
theorem unsat1706 : Unsatisfiable (PosFin 57) f1706 := by
  apply lratCheckerSound f1706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1706
  · intro a ha; simp [p1706] at ha; subst a; trivial
  · exact checked1706
theorem derived1706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1706 := by
  apply localUnsat_implies_entails f1706 [c1705, c1699, c1703, c275] c1706 unsat1706 (by rfl) a
  have h0 : Entails.eval a c1705 := derived1705 a h
  have h1 : Entails.eval a c1699 := derived1699 a h
  have h2 : Entails.eval a c1703 := derived1703 a h
  have h3 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1707 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1705, some c1697, some c1699, some c270, some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1707 : lratChecker f1707 p1707 = .success := by decide +kernel
theorem unsat1707 : Unsatisfiable (PosFin 57) f1707 := by
  apply lratCheckerSound f1707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1707
  · intro a ha; simp [p1707] at ha; subst a; trivial
  · exact checked1707
theorem derived1707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1707 := by
  apply localUnsat_implies_entails f1707 [c1705, c1697, c1699, c270] c1707 unsat1707 (by rfl) a
  have h0 : Entails.eval a c1705 := derived1705 a h
  have h1 : Entails.eval a c1697 := derived1697 a h
  have h2 : Entails.eval a c1699 := derived1699 a h
  have h3 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1708 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1706, some c1702, some c1707, some c221, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1708 : lratChecker f1708 p1708 = .success := by decide +kernel
theorem unsat1708 : Unsatisfiable (PosFin 57) f1708 := by
  apply lratCheckerSound f1708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1708
  · intro a ha; simp [p1708] at ha; subst a; trivial
  · exact checked1708
theorem derived1708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1708 := by
  apply localUnsat_implies_entails f1708 [c1706, c1702, c1707, c221] c1708 unsat1708 (by rfl) a
  have h0 : Entails.eval a c1706 := derived1706 a h
  have h1 : Entails.eval a c1702 := derived1702 a h
  have h2 : Entails.eval a c1707 := derived1707 a h
  have h3 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1709 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1707, some c1695, some c1486, some c62, some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1709 : lratChecker f1709 p1709 = .success := by decide +kernel
theorem unsat1709 : Unsatisfiable (PosFin 57) f1709 := by
  apply lratCheckerSound f1709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1709
  · intro a ha; simp [p1709] at ha; subst a; trivial
  · exact checked1709
theorem derived1709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1709 := by
  apply localUnsat_implies_entails f1709 [c1707, c1695, c1486, c62] c1709 unsat1709 (by rfl) a
  have h0 : Entails.eval a c1707 := derived1707 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  have h2 : Entails.eval a c1486 := derived1486 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1710 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1708, some c1701, some c263, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1710 : lratChecker f1710 p1710 = .success := by decide +kernel
theorem unsat1710 : Unsatisfiable (PosFin 57) f1710 := by
  apply lratCheckerSound f1710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1710
  · intro a ha; simp [p1710] at ha; subst a; trivial
  · exact checked1710
theorem derived1710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1710 := by
  apply localUnsat_implies_entails f1710 [c1708, c1701, c263] c1710 unsat1710 (by rfl) a
  have h0 : Entails.eval a c1708 := derived1708 a h
  have h1 : Entails.eval a c1701 := derived1701 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1711 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1709, some c1704, some c356, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1711 : lratChecker f1711 p1711 = .success := by decide +kernel
theorem unsat1711 : Unsatisfiable (PosFin 57) f1711 := by
  apply lratCheckerSound f1711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1711
  · intro a ha; simp [p1711] at ha; subst a; trivial
  · exact checked1711
theorem derived1711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1711 := by
  apply localUnsat_implies_entails f1711 [c1709, c1704, c356] c1711 unsat1711 (by rfl) a
  have h0 : Entails.eval a c1709 := derived1709 a h
  have h1 : Entails.eval a c1704 := derived1704 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1712 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1710, some c1711, some c1702, some c1706, some c225]
def p1712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1712 : lratChecker f1712 p1712 = .success := by decide +kernel
theorem unsat1712 : Unsatisfiable (PosFin 57) f1712 := by
  apply lratCheckerSound f1712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1712
  · intro a ha; simp [p1712] at ha; subst a; trivial
  · exact checked1712
theorem derived1712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1712 := by
  apply localUnsat_implies_entails f1712 [c1710, c1711, c1702, c1706, c225] c1712 unsat1712 (by rfl) a
  have h0 : Entails.eval a c1710 := derived1710 a h
  have h1 : Entails.eval a c1711 := derived1711 a h
  have h2 : Entails.eval a c1702 := derived1702 a h
  have h3 : Entails.eval a c1706 := derived1706 a h
  have h4 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1712

end CochromaticTwenty.Certificates.B16_7_2
