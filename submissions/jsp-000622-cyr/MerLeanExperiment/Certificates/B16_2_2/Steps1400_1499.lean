import MerLeanExperiment.Certificates.B16_2_2.Steps1300_1399

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1784 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1782, some c189, some c1757, some c1003, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1784 : lratChecker f1784 p1784 = .success := by decide +kernel
theorem unsat1784 : Unsatisfiable (PosFin 57) f1784 := by
  apply lratCheckerSound f1784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1784
  · intro a ha; simp [p1784] at ha; subst a; trivial
  · exact checked1784
theorem derived1784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1784 := by
  apply localUnsat_implies_entails f1784 [c1782, c189, c1757, c1003] c1784 unsat1784 (by rfl) a
  have h0 : Entails.eval a c1782 := derived1782 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c1757 := derived1757 a h
  have h3 : Entails.eval a c1003 := derived1003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1785 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1753, some c100, some c97, some c1531, some c380, some c182, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1785 : lratChecker f1785 p1785 = .success := by decide +kernel
theorem unsat1785 : Unsatisfiable (PosFin 57) f1785 := by
  apply lratCheckerSound f1785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1785
  · intro a ha; simp [p1785] at ha; subst a; trivial
  · exact checked1785
theorem derived1785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1785 := by
  apply localUnsat_implies_entails f1785 [c1753, c100, c97, c1531, c380, c182] c1785 unsat1785 (by rfl) a
  have h0 : Entails.eval a c1753 := derived1753 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c1531 := derived1531 a h
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1786 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1782, some c1783, some c1, some c9, some c11, some c1713, some c193, some c1785, some c1003, some c1714, some c1629, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1786 : lratChecker f1786 p1786 = .success := by decide +kernel
theorem unsat1786 : Unsatisfiable (PosFin 57) f1786 := by
  apply lratCheckerSound f1786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1786
  · intro a ha; simp [p1786] at ha; subst a; trivial
  · exact checked1786
theorem derived1786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1786 := by
  apply localUnsat_implies_entails f1786 [c1668, c1782, c1783, c1, c9, c11, c1713, c193, c1785, c1003, c1714, c1629] c1786 unsat1786 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1782 := derived1782 a h
  have h2 : Entails.eval a c1783 := derived1783 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c1713 := derived1713 a h
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c1785 := derived1785 a h
  have h9 : Entails.eval a c1003 := derived1003 a h
  have h10 : Entails.eval a c1714 := derived1714 a h
  have h11 : Entails.eval a c1629 := derived1629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1787 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1753, some c1782, some c1786, some c189, some c1784, some c1003, some c5, some c12, some c79, some c97, some c1771, some c1727, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1787 : lratChecker f1787 p1787 = .success := by decide +kernel
theorem unsat1787 : Unsatisfiable (PosFin 57) f1787 := by
  apply lratCheckerSound f1787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1787
  · intro a ha; simp [p1787] at ha; subst a; trivial
  · exact checked1787
theorem derived1787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1787 := by
  apply localUnsat_implies_entails f1787 [c1753, c1782, c1786, c189, c1784, c1003, c5, c12, c79, c97, c1771, c1727] c1787 unsat1787 (by rfl) a
  have h0 : Entails.eval a c1753 := derived1753 a h
  have h1 : Entails.eval a c1782 := derived1782 a h
  have h2 : Entails.eval a c1786 := derived1786 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c1784 := derived1784 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c1771 := derived1771 a h
  have h11 : Entails.eval a c1727 := derived1727 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1788 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1787, some c1783, some c1753, some c191, some c1314, some c1354, some c110, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1788 : lratChecker f1788 p1788 = .success := by decide +kernel
theorem unsat1788 : Unsatisfiable (PosFin 57) f1788 := by
  apply lratCheckerSound f1788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1788
  · intro a ha; simp [p1788] at ha; subst a; trivial
  · exact checked1788
theorem derived1788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1788 := by
  apply localUnsat_implies_entails f1788 [c1787, c1783, c1753, c191, c1314, c1354, c110] c1788 unsat1788 (by rfl) a
  have h0 : Entails.eval a c1787 := derived1787 a h
  have h1 : Entails.eval a c1783 := derived1783 a h
  have h2 : Entails.eval a c1753 := derived1753 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c1314 := derived1314 a h
  have h5 : Entails.eval a c1354 := derived1354 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1789 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1753, some c1783, some c1787, some c1721, some c5, some c1003, some c100, some c382, some c79, some c1727, some c19, some c183, some c110, some c377, some c104, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1789 : lratChecker f1789 p1789 = .success := by decide +kernel
theorem unsat1789 : Unsatisfiable (PosFin 57) f1789 := by
  apply lratCheckerSound f1789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1789
  · intro a ha; simp [p1789] at ha; subst a; trivial
  · exact checked1789
theorem derived1789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1789 := by
  apply localUnsat_implies_entails f1789 [c1753, c1783, c1787, c1721, c5, c1003, c100, c382, c79, c1727, c19, c183, c110, c377, c104] c1789 unsat1789 (by rfl) a
  have h0 : Entails.eval a c1753 := derived1753 a h
  have h1 : Entails.eval a c1783 := derived1783 a h
  have h2 : Entails.eval a c1787 := derived1787 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c1727 := derived1727 a h
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1790 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c241, some c252, some c31, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1790 : lratChecker f1790 p1790 = .success := by decide +kernel
theorem unsat1790 : Unsatisfiable (PosFin 57) f1790 := by
  apply lratCheckerSound f1790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1790
  · intro a ha; simp [p1790] at ha; subst a; trivial
  · exact checked1790
theorem derived1790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1790 := by
  apply localUnsat_implies_entails f1790 [c1668, c241, c252, c31] c1790 unsat1790 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1791 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1783, some c1787, some c1721, some c1003, some c79, some c1753, some c5, some c100, some c1727, some c1790, some c25, some c368, some c83, some c375, some c382, some c1788, some c11, some c1789, some c176, some c690, some c362, some c377, some c173, some c182, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1791 : lratChecker f1791 p1791 = .success := by decide +kernel
theorem unsat1791 : Unsatisfiable (PosFin 57) f1791 := by
  apply lratCheckerSound f1791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1791
  · intro a ha; simp [p1791] at ha; subst a; trivial
  · exact checked1791
theorem derived1791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1791 := by
  apply localUnsat_implies_entails f1791 [c1668, c1783, c1787, c1721, c1003, c79, c1753, c5, c100, c1727, c1790, c25, c368, c83, c375, c382, c1788, c11, c1789, c176, c690, c362, c377, c173, c182] c1791 unsat1791 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1783 := derived1783 a h
  have h2 : Entails.eval a c1787 := derived1787 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c1753 := derived1753 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1727 := derived1727 a h
  have h10 : Entails.eval a c1790 := derived1790 a h
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c1788 := derived1788 a h
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c1789 := derived1789 a h
  have h19 : Entails.eval a c176 := h 175 (by decide)
  have h20 : Entails.eval a c690 := derived690 a h
  have h21 : Entails.eval a c362 := h 361 (by decide)
  have h22 : Entails.eval a c377 := h 376 (by decide)
  have h23 : Entails.eval a c173 := h 172 (by decide)
  have h24 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1792 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1783, some c1787, some c1721, some c1003, some c79, some c1753, some c5, some c100, some c1727, some c1790, some c25, some c368, some c21, some c1314, some c115, some c110, some c1072, some c104, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1792 : lratChecker f1792 p1792 = .success := by decide +kernel
theorem unsat1792 : Unsatisfiable (PosFin 57) f1792 := by
  apply lratCheckerSound f1792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1792
  · intro a ha; simp [p1792] at ha; subst a; trivial
  · exact checked1792
theorem derived1792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1792 := by
  apply localUnsat_implies_entails f1792 [c1668, c1783, c1787, c1721, c1003, c79, c1753, c5, c100, c1727, c1790, c25, c368, c21, c1314, c115, c110, c1072, c104] c1792 unsat1792 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1783 := derived1783 a h
  have h2 : Entails.eval a c1787 := derived1787 a h
  have h3 : Entails.eval a c1721 := derived1721 a h
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c1753 := derived1753 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1727 := derived1727 a h
  have h10 : Entails.eval a c1790 := derived1790 a h
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c1314 := derived1314 a h
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c1072 := derived1072 a h
  have h18 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1793 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c361, some c234, some c242, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1793 : lratChecker f1793 p1793 = .success := by decide +kernel
theorem unsat1793 : Unsatisfiable (PosFin 57) f1793 := by
  apply lratCheckerSound f1793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1793
  · intro a ha; simp [p1793] at ha; subst a; trivial
  · exact checked1793
theorem derived1793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1793 := by
  apply localUnsat_implies_entails f1793 [c361, c234, c242] c1793 unsat1793 (by rfl) a
  have h0 : Entails.eval a c361 := h 360 (by decide)
  have h1 : Entails.eval a c234 := h 233 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1794 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1783, some c1787, some c1721, some c1003, some c5, some c79, some c100, some c1727, some c382, some c1790, some c25, some c375, some c368, some c83, some c21, some c1791, some c1792, some c11, some c1274, some c1793, some c173, some c18, some c110, some c1317, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1794 : lratChecker f1794 p1794 = .success := by decide +kernel
theorem unsat1794 : Unsatisfiable (PosFin 57) f1794 := by
  apply lratCheckerSound f1794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1794
  · intro a ha; simp [p1794] at ha; subst a; trivial
  · exact checked1794
theorem derived1794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1794 := by
  apply localUnsat_implies_entails f1794 [c1668, c1753, c1783, c1787, c1721, c1003, c5, c79, c100, c1727, c382, c1790, c25, c375, c368, c83, c21, c1791, c1792, c11, c1274, c1793, c173, c18, c110, c1317] c1794 unsat1794 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1783 := derived1783 a h
  have h3 : Entails.eval a c1787 := derived1787 a h
  have h4 : Entails.eval a c1721 := derived1721 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1727 := derived1727 a h
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c1790 := derived1790 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c375 := h 374 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c1791 := derived1791 a h
  have h18 : Entails.eval a c1792 := derived1792 a h
  have h19 : Entails.eval a c11 := h 10 (by decide)
  have h20 : Entails.eval a c1274 := derived1274 a h
  have h21 : Entails.eval a c1793 := derived1793 a h
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  have h24 : Entails.eval a c110 := h 109 (by decide)
  have h25 : Entails.eval a c1317 := derived1317 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1795 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c7, some c1003, some c1753, some c378, some c376, some c103, some c96, some c77, some c512, some c1776, some c81, some c21, some c113, some c1680, some c32, some c23, some c1781, some c1755, some c1774, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1795 : lratChecker f1795 p1795 = .success := by decide +kernel
theorem unsat1795 : Unsatisfiable (PosFin 57) f1795 := by
  apply lratCheckerSound f1795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1795
  · intro a ha; simp [p1795] at ha; subst a; trivial
  · exact checked1795
theorem derived1795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1795 := by
  apply localUnsat_implies_entails f1795 [c1668, c1794, c13, c7, c1003, c1753, c378, c376, c103, c96, c77, c512, c1776, c81, c21, c113, c1680, c32, c23, c1781, c1755, c1774] c1795 unsat1795 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c512 := derived512 a h
  have h12 : Entails.eval a c1776 := derived1776 a h
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c1680 := derived1680 a h
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c23 := h 22 (by decide)
  have h19 : Entails.eval a c1781 := derived1781 a h
  have h20 : Entails.eval a c1755 := derived1755 a h
  have h21 : Entails.eval a c1774 := derived1774 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1796 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨47, by decide⟩, false), (⟨23, by decide⟩, true), (⟨42, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1254, some c193, some c1005, some c194, some c1755, some c1729, some c55, some c53, some c145, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1796 : lratChecker f1796 p1796 = .success := by decide +kernel
theorem unsat1796 : Unsatisfiable (PosFin 57) f1796 := by
  apply lratCheckerSound f1796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1796
  · intro a ha; simp [p1796] at ha; subst a; trivial
  · exact checked1796
theorem derived1796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1796 := by
  apply localUnsat_implies_entails f1796 [c1668, c1254, c193, c1005, c194, c1755, c1729, c55, c53, c145] c1796 unsat1796 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c193 := h 192 (by decide)
  have h3 : Entails.eval a c1005 := derived1005 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1755 := derived1755 a h
  have h6 : Entails.eval a c1729 := derived1729 a h
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1797 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c7, some c1003, some c1753, some c1795, some c73, some c515, some c93, some c161, some c383, some c84, some c25, some c254, some c27, some c33, some c370, some c91, some c1796, some c182, some c705, some c380, some c247, some c364, some c1612, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1797 : lratChecker f1797 p1797 = .success := by decide +kernel
theorem unsat1797 : Unsatisfiable (PosFin 57) f1797 := by
  apply lratCheckerSound f1797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1797
  · intro a ha; simp [p1797] at ha; subst a; trivial
  · exact checked1797
theorem derived1797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1797 := by
  apply localUnsat_implies_entails f1797 [c1668, c1794, c13, c7, c1003, c1753, c1795, c73, c515, c93, c161, c383, c84, c25, c254, c27, c33, c370, c91, c1796, c182, c705, c380, c247, c364, c1612] c1797 unsat1797 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c1795 := derived1795 a h
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c515 := derived515 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c383 := h 382 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c33 := h 32 (by decide)
  have h17 : Entails.eval a c370 := h 369 (by decide)
  have h18 : Entails.eval a c91 := h 90 (by decide)
  have h19 : Entails.eval a c1796 := derived1796 a h
  have h20 : Entails.eval a c182 := h 181 (by decide)
  have h21 : Entails.eval a c705 := derived705 a h
  have h22 : Entails.eval a c380 := h 379 (by decide)
  have h23 : Entails.eval a c247 := h 246 (by decide)
  have h24 : Entails.eval a c364 := h 363 (by decide)
  have h25 : Entails.eval a c1612 := derived1612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1798 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c7, some c1003, some c1753, some c378, some c376, some c96, some c77, some c512, some c81, some c21, some c113, some c1680, some c32, some c658, some c245, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1798 : lratChecker f1798 p1798 = .success := by decide +kernel
theorem unsat1798 : Unsatisfiable (PosFin 57) f1798 := by
  apply lratCheckerSound f1798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1798
  · intro a ha; simp [p1798] at ha; subst a; trivial
  · exact checked1798
theorem derived1798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1798 := by
  apply localUnsat_implies_entails f1798 [c1668, c1794, c13, c7, c1003, c1753, c378, c376, c96, c77, c512, c81, c21, c113, c1680, c32, c658, c245] c1798 unsat1798 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c512 := derived512 a h
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c1680 := derived1680 a h
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c658 := derived658 a h
  have h17 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1799 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c7, some c1003, some c1753, some c1798, some c73, some c515, some c93, some c161, some c383, some c84, some c25, some c263, some c264, some c27, some c370, some c700, some c693, some c372, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1799 : lratChecker f1799 p1799 = .success := by decide +kernel
theorem unsat1799 : Unsatisfiable (PosFin 57) f1799 := by
  apply lratCheckerSound f1799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1799
  · intro a ha; simp [p1799] at ha; subst a; trivial
  · exact checked1799
theorem derived1799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1799 := by
  apply localUnsat_implies_entails f1799 [c1668, c1794, c7, c1003, c1753, c1798, c73, c515, c93, c161, c383, c84, c25, c263, c264, c27, c370, c700, c693, c372] c1799 unsat1799 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1753 := derived1753 a h
  have h5 : Entails.eval a c1798 := derived1798 a h
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c370 := h 369 (by decide)
  have h17 : Entails.eval a c700 := derived700 a h
  have h18 : Entails.eval a c693 := derived693 a h
  have h19 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1800 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨48, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c16, some c7, some c1003, some c1753, some c376, some c1714, some c512, some c172, some c83, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1800 : lratChecker f1800 p1800 = .success := by decide +kernel
theorem unsat1800 : Unsatisfiable (PosFin 57) f1800 := by
  apply lratCheckerSound f1800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1800
  · intro a ha; simp [p1800] at ha; subst a; trivial
  · exact checked1800
theorem derived1800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1800 := by
  apply localUnsat_implies_entails f1800 [c1668, c1794, c16, c7, c1003, c1753, c376, c1714, c512, c172, c83] c1800 unsat1800 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c1714 := derived1714 a h
  have h8 : Entails.eval a c512 := derived512 a h
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1801 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c7, some c1753, some c1799, some c1797, some c16, some c1713, some c193, some c1800, some c515, some c93, some c95, some c705, some c1776, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1801 : lratChecker f1801 p1801 = .success := by decide +kernel
theorem unsat1801 : Unsatisfiable (PosFin 57) f1801 := by
  apply lratCheckerSound f1801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1801
  · intro a ha; simp [p1801] at ha; subst a; trivial
  · exact checked1801
theorem derived1801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1801 := by
  apply localUnsat_implies_entails f1801 [c1668, c1794, c13, c7, c1753, c1799, c1797, c16, c1713, c193, c1800, c515, c93, c95, c705, c1776] c1801 unsat1801 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1753 := derived1753 a h
  have h5 : Entails.eval a c1799 := derived1799 a h
  have h6 : Entails.eval a c1797 := derived1797 a h
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c1713 := derived1713 a h
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c1800 := derived1800 a h
  have h11 : Entails.eval a c515 := derived515 a h
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c705 := derived705 a h
  have h15 : Entails.eval a c1776 := derived1776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1802 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1794, some c7, some c1801, some c1, some c378, some c13, some c376, some c96, some c1776, some c77, some c103, some c1769, some c368, some c1775, some c21, some c33, some c243, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1802 : lratChecker f1802 p1802 = .success := by decide +kernel
theorem unsat1802 : Unsatisfiable (PosFin 57) f1802 := by
  apply lratCheckerSound f1802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1802
  · intro a ha; simp [p1802] at ha; subst a; trivial
  · exact checked1802
theorem derived1802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1802 := by
  apply localUnsat_implies_entails f1802 [c1668, c1753, c1794, c7, c1801, c1, c378, c13, c376, c96, c1776, c77, c103, c1769, c368, c1775, c21, c33, c243] c1802 unsat1802 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1801 := derived1801 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c1776 := derived1776 a h
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c1769 := derived1769 a h
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c1775 := derived1775 a h
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c33 := h 32 (by decide)
  have h18 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1803 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1794, some c7, some c1801, some c1, some c378, some c13, some c376, some c96, some c1776, some c103, some c1802, some c85, some c27, some c1775, some c243, some c29, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1803 : lratChecker f1803 p1803 = .success := by decide +kernel
theorem unsat1803 : Unsatisfiable (PosFin 57) f1803 := by
  apply lratCheckerSound f1803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1803
  · intro a ha; simp [p1803] at ha; subst a; trivial
  · exact checked1803
theorem derived1803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1803 := by
  apply localUnsat_implies_entails f1803 [c1668, c1753, c1794, c7, c1801, c1, c378, c13, c376, c96, c1776, c103, c1802, c85, c27, c1775, c243, c29] c1803 unsat1803 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1801 := derived1801 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c1776 := derived1776 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c1802 := derived1802 a h
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c1775 := derived1775 a h
  have h16 : Entails.eval a c243 := h 242 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1804 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1794, some c7, some c1801, some c1, some c376, some c77, some c96, some c378, some c13, some c1003, some c664, some c32, some c245, some c260, some c183, some c1702, some c120, some c362, some c1414, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1804 : lratChecker f1804 p1804 = .success := by decide +kernel
theorem unsat1804 : Unsatisfiable (PosFin 57) f1804 := by
  apply lratCheckerSound f1804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1804
  · intro a ha; simp [p1804] at ha; subst a; trivial
  · exact checked1804
theorem derived1804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1804 := by
  apply localUnsat_implies_entails f1804 [c1668, c1753, c1794, c7, c1801, c1, c376, c77, c96, c378, c13, c1003, c664, c32, c245, c260, c183, c1702, c120, c362, c1414] c1804 unsat1804 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1801 := derived1801 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1003 := derived1003 a h
  have h12 : Entails.eval a c664 := derived664 a h
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c1702 := derived1702 a h
  have h18 : Entails.eval a c120 := h 119 (by decide)
  have h19 : Entails.eval a c362 := h 361 (by decide)
  have h20 : Entails.eval a c1414 := derived1414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1805 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c7, some c1003, some c1753, some c13, some c1801, some c1, some c378, some c376, some c96, some c77, some c1776, some c1804, some c1803, some c16, some c76, some c172, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1805 : lratChecker f1805 p1805 = .success := by decide +kernel
theorem unsat1805 : Unsatisfiable (PosFin 57) f1805 := by
  apply lratCheckerSound f1805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1805
  · intro a ha; simp [p1805] at ha; subst a; trivial
  · exact checked1805
theorem derived1805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1805 := by
  apply localUnsat_implies_entails f1805 [c1668, c1794, c7, c1003, c1753, c13, c1801, c1, c378, c376, c96, c77, c1776, c1804, c1803, c16, c76, c172] c1805 unsat1805 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1753 := derived1753 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c1801 := derived1801 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c1776 := derived1776 a h
  have h13 : Entails.eval a c1804 := derived1804 a h
  have h14 : Entails.eval a c1803 := derived1803 a h
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1806 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1031, some c102, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1806 : lratChecker f1806 p1806 = .success := by decide +kernel
theorem unsat1806 : Unsatisfiable (PosFin 57) f1806 := by
  apply lratCheckerSound f1806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1806
  · intro a ha; simp [p1806] at ha; subst a; trivial
  · exact checked1806
theorem derived1806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1806 := by
  apply localUnsat_implies_entails f1806 [c1668, c1031, c102] c1806 unsat1806 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1031 := derived1031 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1807 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1805, some c1794, some c7, some c1003, some c1753, some c109, some c108, some c3, some c383, some c1806, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1807 : lratChecker f1807 p1807 = .success := by decide +kernel
theorem unsat1807 : Unsatisfiable (PosFin 57) f1807 := by
  apply lratCheckerSound f1807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1807
  · intro a ha; simp [p1807] at ha; subst a; trivial
  · exact checked1807
theorem derived1807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1807 := by
  apply localUnsat_implies_entails f1807 [c1805, c1794, c7, c1003, c1753, c109, c108, c3, c383, c1806] c1807 unsat1807 (by rfl) a
  have h0 : Entails.eval a c1805 := derived1805 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c1753 := derived1753 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c1806 := derived1806 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1808 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c7, some c1003, some c1753, some c378, some c376, some c103, some c1806, some c110, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1808 : lratChecker f1808 p1808 = .success := by decide +kernel
theorem unsat1808 : Unsatisfiable (PosFin 57) f1808 := by
  apply lratCheckerSound f1808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1808
  · intro a ha; simp [p1808] at ha; subst a; trivial
  · exact checked1808
theorem derived1808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1808 := by
  apply localUnsat_implies_entails f1808 [c1794, c7, c1003, c1753, c378, c376, c103, c1806, c110] c1808 unsat1808 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c1753 := derived1753 a h
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c1806 := derived1806 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1809 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1805, some c1794, some c7, some c1003, some c1753, some c1807, some c1808, some c73, some c515, some c161, some c1039, some c25, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1809 : lratChecker f1809 p1809 = .success := by decide +kernel
theorem unsat1809 : Unsatisfiable (PosFin 57) f1809 := by
  apply lratCheckerSound f1809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1809
  · intro a ha; simp [p1809] at ha; subst a; trivial
  · exact checked1809
theorem derived1809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1809 := by
  apply localUnsat_implies_entails f1809 [c1668, c1805, c1794, c7, c1003, c1753, c1807, c1808, c73, c515, c161, c1039, c25] c1809 unsat1809 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1805 := derived1805 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c1807 := derived1807 a h
  have h7 : Entails.eval a c1808 := derived1808 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c515 := derived515 a h
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c1039 := derived1039 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1810 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c7, some c1753, some c1805, some c1809, some c1, some c10, some c1337, some c378, some c376, some c1254, some c103, some c110, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1810 : lratChecker f1810 p1810 = .success := by decide +kernel
theorem unsat1810 : Unsatisfiable (PosFin 57) f1810 := by
  apply lratCheckerSound f1810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1810
  · intro a ha; simp [p1810] at ha; subst a; trivial
  · exact checked1810
theorem derived1810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1810 := by
  apply localUnsat_implies_entails f1810 [c1668, c1794, c7, c1753, c1805, c1809, c1, c10, c1337, c378, c376, c1254, c103, c110] c1810 unsat1810 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1753 := derived1753 a h
  have h4 : Entails.eval a c1805 := derived1805 a h
  have h5 : Entails.eval a c1809 := derived1809 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1337 := derived1337 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c1254 := derived1254 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1811 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c7, some c1003, some c1810, some c195, some c1753, some c378, some c376, some c96, some c512, some c447, some c21, some c113, some c32, some c117, some c1781, some c185, some c1237, some c1531, some c361, some c362, some c1711, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1811 : lratChecker f1811 p1811 = .success := by decide +kernel
theorem unsat1811 : Unsatisfiable (PosFin 57) f1811 := by
  apply lratCheckerSound f1811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1811
  · intro a ha; simp [p1811] at ha; subst a; trivial
  · exact checked1811
theorem derived1811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1811 := by
  apply localUnsat_implies_entails f1811 [c1668, c1794, c13, c7, c1003, c1810, c195, c1753, c378, c376, c96, c512, c447, c21, c113, c32, c117, c1781, c185, c1237, c1531, c361, c362, c1711] c1811 unsat1811 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1810 := derived1810 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c1753 := derived1753 a h
  have h8 : Entails.eval a c378 := h 377 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c512 := derived512 a h
  have h12 : Entails.eval a c447 := derived447 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c1781 := derived1781 a h
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c1237 := derived1237 a h
  have h20 : Entails.eval a c1531 := derived1531 a h
  have h21 : Entails.eval a c361 := h 360 (by decide)
  have h22 : Entails.eval a c362 := h 361 (by decide)
  have h23 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1812 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1810, some c1794, some c7, some c1003, some c1753, some c13, some c1811, some c73, some c515, some c93, some c161, some c383, some c84, some c25, some c165, some c122, some c254, some c27, some c33, some c370, some c362, some c235, some c248, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1812 : lratChecker f1812 p1812 = .success := by decide +kernel
theorem unsat1812 : Unsatisfiable (PosFin 57) f1812 := by
  apply lratCheckerSound f1812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1812
  · intro a ha; simp [p1812] at ha; subst a; trivial
  · exact checked1812
theorem derived1812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1812 := by
  apply localUnsat_implies_entails f1812 [c1668, c1810, c1794, c7, c1003, c1753, c13, c1811, c73, c515, c93, c161, c383, c84, c25, c165, c122, c254, c27, c33, c370, c362, c235, c248] c1812 unsat1812 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1810 := derived1810 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c1753 := derived1753 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c1811 := derived1811 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c515 := derived515 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c383 := h 382 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c370 := h 369 (by decide)
  have h21 : Entails.eval a c362 := h 361 (by decide)
  have h22 : Entails.eval a c235 := h 234 (by decide)
  have h23 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1813 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c7, some c1003, some c1810, some c195, some c1341, some c1753, some c1812, some c109, some c108, some c1254, some c20, some c1385, some c1392, some c190, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1813 : lratChecker f1813 p1813 = .success := by decide +kernel
theorem unsat1813 : Unsatisfiable (PosFin 57) f1813 := by
  apply lratCheckerSound f1813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1813
  · intro a ha; simp [p1813] at ha; subst a; trivial
  · exact checked1813
theorem derived1813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1813 := by
  apply localUnsat_implies_entails f1813 [c1794, c7, c1003, c1810, c195, c1341, c1753, c1812, c109, c108, c1254, c20, c1385, c1392, c190] c1813 unsat1813 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c1810 := derived1810 a h
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c1341 := derived1341 a h
  have h6 : Entails.eval a c1753 := derived1753 a h
  have h7 : Entails.eval a c1812 := derived1812 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c1254 := derived1254 a h
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c1385 := derived1385 a h
  have h13 : Entails.eval a c1392 := derived1392 a h
  have h14 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1814 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c13, some c1753, some c1810, some c7, some c1813, some c1, some c376, some c447, some c1702, some c1781, some c235, some c29, some c33, some c259, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1814 : lratChecker f1814 p1814 = .success := by decide +kernel
theorem unsat1814 : Unsatisfiable (PosFin 57) f1814 := by
  apply lratCheckerSound f1814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1814
  · intro a ha; simp [p1814] at ha; subst a; trivial
  · exact checked1814
theorem derived1814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1814 := by
  apply localUnsat_implies_entails f1814 [c1668, c1794, c13, c1753, c1810, c7, c1813, c1, c376, c447, c1702, c1781, c235, c29, c33, c259] c1814 unsat1814 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c1753 := derived1753 a h
  have h4 : Entails.eval a c1810 := derived1810 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c1813 := derived1813 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c447 := derived447 a h
  have h10 : Entails.eval a c1702 := derived1702 a h
  have h11 : Entails.eval a c1781 := derived1781 a h
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1815 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1794, some c7, some c1813, some c1, some c376, some c1753, some c96, some c1810, some c447, some c378, some c1003, some c195, some c185, some c1237, some c1531, some c361, some c362, some c1711, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1815 : lratChecker f1815 p1815 = .success := by decide +kernel
theorem unsat1815 : Unsatisfiable (PosFin 57) f1815 := by
  apply lratCheckerSound f1815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1815
  · intro a ha; simp [p1815] at ha; subst a; trivial
  · exact checked1815
theorem derived1815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1815 := by
  apply localUnsat_implies_entails f1815 [c1668, c1794, c7, c1813, c1, c376, c1753, c96, c1810, c447, c378, c1003, c195, c185, c1237, c1531, c361, c362, c1711] c1815 unsat1815 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1794 := derived1794 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c1813 := derived1813 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c1753 := derived1753 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1810 := derived1810 a h
  have h9 : Entails.eval a c447 := derived447 a h
  have h10 : Entails.eval a c378 := h 377 (by decide)
  have h11 : Entails.eval a c1003 := derived1003 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c1237 := derived1237 a h
  have h15 : Entails.eval a c1531 := derived1531 a h
  have h16 : Entails.eval a c361 := h 360 (by decide)
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1816 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1810, some c1794, some c7, some c1813, some c1, some c376, some c447, some c378, some c13, some c1815, some c1702, some c1814, some c362, some c117, some c251, some c33, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1816 : lratChecker f1816 p1816 = .success := by decide +kernel
theorem unsat1816 : Unsatisfiable (PosFin 57) f1816 := by
  apply lratCheckerSound f1816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1816
  · intro a ha; simp [p1816] at ha; subst a; trivial
  · exact checked1816
theorem derived1816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1816 := by
  apply localUnsat_implies_entails f1816 [c1668, c1753, c1810, c1794, c7, c1813, c1, c376, c447, c378, c13, c1815, c1702, c1814, c362, c117, c251, c33] c1816 unsat1816 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1810 := derived1810 a h
  have h3 : Entails.eval a c1794 := derived1794 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c1813 := derived1813 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c447 := derived447 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1815 := derived1815 a h
  have h12 : Entails.eval a c1702 := derived1702 a h
  have h13 : Entails.eval a c1814 := derived1814 a h
  have h14 : Entails.eval a c362 := h 361 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c251 := h 250 (by decide)
  have h17 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1817 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1753, some c1794, some c7, some c1810, some c1341, some c1813, some c1, some c376, some c77, some c447, some c1816, some c108, some c82, some c583, some c368, some c27, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1817 : lratChecker f1817 p1817 = .success := by decide +kernel
theorem unsat1817 : Unsatisfiable (PosFin 57) f1817 := by
  apply lratCheckerSound f1817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1817
  · intro a ha; simp [p1817] at ha; subst a; trivial
  · exact checked1817
theorem derived1817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1817 := by
  apply localUnsat_implies_entails f1817 [c1668, c1753, c1794, c7, c1810, c1341, c1813, c1, c376, c77, c447, c1816, c108, c82, c583, c368, c27] c1817 unsat1817 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1753 := derived1753 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c1810 := derived1810 a h
  have h5 : Entails.eval a c1341 := derived1341 a h
  have h6 : Entails.eval a c1813 := derived1813 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c447 := derived447 a h
  have h11 : Entails.eval a c1816 := derived1816 a h
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c82 := h 81 (by decide)
  have h14 : Entails.eval a c583 := derived583 a h
  have h15 : Entails.eval a c368 := h 367 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1818 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c56, some c54, some c147, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1818 : lratChecker f1818 p1818 = .success := by decide +kernel
theorem unsat1818 : Unsatisfiable (PosFin 57) f1818 := by
  apply lratCheckerSound f1818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1818
  · intro a ha; simp [p1818] at ha; subst a; trivial
  · exact checked1818
theorem derived1818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1818 := by
  apply localUnsat_implies_entails f1818 [c1817, c56, c54, c147] c1818 unsat1818 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1819 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨17, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c191, some c115, some c15, some c1818, some c203, some c70, some c72, some c159, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1819 : lratChecker f1819 p1819 = .success := by decide +kernel
theorem unsat1819 : Unsatisfiable (PosFin 57) f1819 := by
  apply lratCheckerSound f1819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1819
  · intro a ha; simp [p1819] at ha; subst a; trivial
  · exact checked1819
theorem derived1819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1819 := by
  apply localUnsat_implies_entails f1819 [c1668, c1817, c112, c10, c191, c115, c15, c1818, c203, c70, c72, c159] c1819 unsat1819 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c1818 := derived1818 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1820 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨53, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c30, some c2, some c841, some c808, some c187, some c339, some c336, some c244, some c223, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1820 : lratChecker f1820 p1820 = .success := by decide +kernel
theorem unsat1820 : Unsatisfiable (PosFin 57) f1820 := by
  apply lratCheckerSound f1820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1820
  · intro a ha; simp [p1820] at ha; subst a; trivial
  · exact checked1820
theorem derived1820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1820 := by
  apply localUnsat_implies_entails f1820 [c1668, c1817, c112, c30, c2, c841, c808, c187, c339, c336, c244, c223] c1820 unsat1820 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c808 := derived808 a h
  have h7 : Entails.eval a c187 := h 186 (by decide)
  have h8 : Entails.eval a c339 := h 338 (by decide)
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1821 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨8, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c112, some c23, some c70, some c325, some c160, some c223, some c71, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1821 : lratChecker f1821 p1821 = .success := by decide +kernel
theorem unsat1821 : Unsatisfiable (PosFin 57) f1821 := by
  apply lratCheckerSound f1821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1821
  · intro a ha; simp [p1821] at ha; subst a; trivial
  · exact checked1821
theorem derived1821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1821 := by
  apply localUnsat_implies_entails f1821 [c1817, c112, c23, c70, c325, c160, c223, c71] c1821 unsat1821 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1822 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1254, some c112, some c30, some c188, some c889, some c1231, some c74, some c187, some c168, some c116, some c942, some c80, some c1821, some c133, some c158, some c54, some c886, some c148, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1822 : lratChecker f1822 p1822 = .success := by decide +kernel
theorem unsat1822 : Unsatisfiable (PosFin 57) f1822 := by
  apply lratCheckerSound f1822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1822
  · intro a ha; simp [p1822] at ha; subst a; trivial
  · exact checked1822
theorem derived1822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1822 := by
  apply localUnsat_implies_entails f1822 [c1668, c1817, c1254, c112, c30, c188, c889, c1231, c74, c187, c168, c116, c942, c80, c1821, c133, c158, c54, c886, c148] c1822 unsat1822 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c889 := derived889 a h
  have h7 : Entails.eval a c1231 := derived1231 a h
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c942 := derived942 a h
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c1821 := derived1821 a h
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  have h17 : Entails.eval a c54 := h 53 (by decide)
  have h18 : Entails.eval a c886 := derived886 a h
  have h19 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1823 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c112, some c15, some c1818, some c135, some c70, some c72, some c159, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1823 : lratChecker f1823 p1823 = .success := by decide +kernel
theorem unsat1823 : Unsatisfiable (PosFin 57) f1823 := by
  apply lratCheckerSound f1823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1823
  · intro a ha; simp [p1823] at ha; subst a; trivial
  · exact checked1823
theorem derived1823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1823 := by
  apply localUnsat_implies_entails f1823 [c1817, c112, c15, c1818, c135, c70, c72, c159] c1823 unsat1823 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c1818 := derived1818 a h
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1824 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c30, some c1819, some c1823, some c190, some c3, some c1820, some c1822, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1824 : lratChecker f1824 p1824 = .success := by decide +kernel
theorem unsat1824 : Unsatisfiable (PosFin 57) f1824 := by
  apply lratCheckerSound f1824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1824
  · intro a ha; simp [p1824] at ha; subst a; trivial
  · exact checked1824
theorem derived1824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1824 := by
  apply localUnsat_implies_entails f1824 [c1668, c1817, c112, c10, c30, c1819, c1823, c190, c3, c1820, c1822] c1824 unsat1824 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1819 := derived1819 a h
  have h6 : Entails.eval a c1823 := derived1823 a h
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c1820 := derived1820 a h
  have h10 : Entails.eval a c1822 := derived1822 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1825 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c1823, some c190, some c3, some c2, some c808, some c336, some c338, some c154, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1825 : lratChecker f1825 p1825 = .success := by decide +kernel
theorem unsat1825 : Unsatisfiable (PosFin 57) f1825 := by
  apply lratCheckerSound f1825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1825
  · intro a ha; simp [p1825] at ha; subst a; trivial
  · exact checked1825
theorem derived1825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1825 := by
  apply localUnsat_implies_entails f1825 [c1668, c1817, c112, c10, c1823, c190, c3, c2, c808, c336, c338, c154] c1825 unsat1825 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1823 := derived1823 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c808 := derived808 a h
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c338 := h 337 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1826 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c30, some c23, some c10, some c3, some c1819, some c1823, some c190, some c116, some c188, some c1231, some c1824, some c382, some c241, some c1825, some c1692, some c364, some c239, some c374, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1826 : lratChecker f1826 p1826 = .success := by decide +kernel
theorem unsat1826 : Unsatisfiable (PosFin 57) f1826 := by
  apply lratCheckerSound f1826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1826
  · intro a ha; simp [p1826] at ha; subst a; trivial
  · exact checked1826
theorem derived1826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1826 := by
  apply localUnsat_implies_entails f1826 [c1817, c1668, c112, c30, c23, c10, c3, c1819, c1823, c190, c116, c188, c1231, c1824, c382, c241, c1825, c1692, c364, c239, c374] c1826 unsat1826 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c1819 := derived1819 a h
  have h8 : Entails.eval a c1823 := derived1823 a h
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c1231 := derived1231 a h
  have h13 : Entails.eval a c1824 := derived1824 a h
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c1825 := derived1825 a h
  have h17 : Entails.eval a c1692 := derived1692 a h
  have h18 : Entails.eval a c364 := h 363 (by decide)
  have h19 : Entails.eval a c239 := h 238 (by decide)
  have h20 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1827 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c374, some c363, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1827 : lratChecker f1827 p1827 = .success := by decide +kernel
theorem unsat1827 : Unsatisfiable (PosFin 57) f1827 := by
  apply lratCheckerSound f1827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1827
  · intro a ha; simp [p1827] at ha; subst a; trivial
  · exact checked1827
theorem derived1827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1827 := by
  apply localUnsat_implies_entails f1827 [c375, c374, c363] c1827 unsat1827 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1828 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c244, some c365, some c239, some c1711, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1828 : lratChecker f1828 p1828 = .success := by decide +kernel
theorem unsat1828 : Unsatisfiable (PosFin 57) f1828 := by
  apply lratCheckerSound f1828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1828
  · intro a ha; simp [p1828] at ha; subst a; trivial
  · exact checked1828
theorem derived1828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1828 := by
  apply localUnsat_implies_entails f1828 [c377, c244, c365, c239, c1711] c1828 unsat1828 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1829 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨45, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1828, some c366, some c1711, some c365, some c238, some c242, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1829 : lratChecker f1829 p1829 = .success := by decide +kernel
theorem unsat1829 : Unsatisfiable (PosFin 57) f1829 := by
  apply lratCheckerSound f1829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1829
  · intro a ha; simp [p1829] at ha; subst a; trivial
  · exact checked1829
theorem derived1829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1829 := by
  apply localUnsat_implies_entails f1829 [c1828, c366, c1711, c365, c238, c242] c1829 unsat1829 (by rfl) a
  have h0 : Entails.eval a c1828 := derived1828 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c1711 := derived1711 a h
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1830 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c244, some c188, some c239, some c114, some c1711, some c238, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1830 : lratChecker f1830 p1830 = .success := by decide +kernel
theorem unsat1830 : Unsatisfiable (PosFin 57) f1830 := by
  apply lratCheckerSound f1830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1830
  · intro a ha; simp [p1830] at ha; subst a; trivial
  · exact checked1830
theorem derived1830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1830 := by
  apply localUnsat_implies_entails f1830 [c377, c244, c188, c239, c114, c1711, c238] c1830 unsat1830 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c244 := h 243 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c1711 := derived1711 a h
  have h6 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1831 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨45, by decide⟩, true), (⟨12, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨21, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c3, some c379, some c30, some c10, some c364, some c80, some c239, some c258, some c259, some c116, some c34, some c238, some c714, some c173, some c55, some c1684, some c143, some c1426, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1831 : lratChecker f1831 p1831 = .success := by decide +kernel
theorem unsat1831 : Unsatisfiable (PosFin 57) f1831 := by
  apply lratCheckerSound f1831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1831
  · intro a ha; simp [p1831] at ha; subst a; trivial
  · exact checked1831
theorem derived1831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1831 := by
  apply localUnsat_implies_entails f1831 [c1668, c1817, c112, c3, c379, c30, c10, c364, c80, c239, c258, c259, c116, c34, c238, c714, c173, c55, c1684, c143, c1426] c1831 unsat1831 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c239 := h 238 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c238 := h 237 (by decide)
  have h15 : Entails.eval a c714 := derived714 a h
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c55 := h 54 (by decide)
  have h18 : Entails.eval a c1684 := derived1684 a h
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c1426 := derived1426 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1832 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c242, some c188, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1832 : lratChecker f1832 p1832 = .success := by decide +kernel
theorem unsat1832 : Unsatisfiable (PosFin 57) f1832 := by
  apply lratCheckerSound f1832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1832
  · intro a ha; simp [p1832] at ha; subst a; trivial
  · exact checked1832
theorem derived1832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1832 := by
  apply localUnsat_implies_entails f1832 [c114, c242, c188] c1832 unsat1832 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c242 := h 241 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1833 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c113, some c189, some c377, some c1830, some c188, some c161, some c375, some c1827, some c81, some c367, some c379, some c167, some c2, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1833 : lratChecker f1833 p1833 = .success := by decide +kernel
theorem unsat1833 : Unsatisfiable (PosFin 57) f1833 := by
  apply lratCheckerSound f1833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1833
  · intro a ha; simp [p1833] at ha; subst a; trivial
  · exact checked1833
theorem derived1833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1833 := by
  apply localUnsat_implies_entails f1833 [c1668, c113, c189, c377, c1830, c188, c161, c375, c1827, c81, c367, c379, c167, c2] c1833 unsat1833 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c1830 := derived1830 a h
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c1827 := derived1827 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1834 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c3, some c10, some c23, some c30, some c1826, some c1833, some c189, some c1832, some c113, some c2, some c379, some c184, some c1827, some c238, some c1831, some c1711, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1834 : lratChecker f1834 p1834 = .success := by decide +kernel
theorem unsat1834 : Unsatisfiable (PosFin 57) f1834 := by
  apply lratCheckerSound f1834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1834
  · intro a ha; simp [p1834] at ha; subst a; trivial
  · exact checked1834
theorem derived1834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1834 := by
  apply localUnsat_implies_entails f1834 [c1668, c1817, c112, c3, c10, c23, c30, c1826, c1833, c189, c1832, c113, c2, c379, c184, c1827, c238, c1831, c1711] c1834 unsat1834 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1826 := derived1826 a h
  have h8 : Entails.eval a c1833 := derived1833 a h
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c1832 := derived1832 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c184 := h 183 (by decide)
  have h15 : Entails.eval a c1827 := derived1827 a h
  have h16 : Entails.eval a c238 := h 237 (by decide)
  have h17 : Entails.eval a c1831 := derived1831 a h
  have h18 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1835 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1834, some c112, some c3, some c10, some c23, some c30, some c1826, some c1833, some c189, some c1832, some c34, some c113, some c1829, some c238, some c382, some c1711, some c184, some c364, some c80, some c239, some c193, some c754, some c259, some c116, some c1684, some c118, some c714, some c324, some c289, some c200, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1835 : lratChecker f1835 p1835 = .success := by decide +kernel
theorem unsat1835 : Unsatisfiable (PosFin 57) f1835 := by
  apply lratCheckerSound f1835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1835
  · intro a ha; simp [p1835] at ha; subst a; trivial
  · exact checked1835
theorem derived1835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1835 := by
  apply localUnsat_implies_entails f1835 [c1668, c1817, c1834, c112, c3, c10, c23, c30, c1826, c1833, c189, c1832, c34, c113, c1829, c238, c382, c1711, c184, c364, c80, c239, c193, c754, c259, c116, c1684, c118, c714, c324, c289, c200] c1835 unsat1835 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1834 := derived1834 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c1826 := derived1826 a h
  have h9 : Entails.eval a c1833 := derived1833 a h
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c1832 := derived1832 a h
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c1829 := derived1829 a h
  have h15 : Entails.eval a c238 := h 237 (by decide)
  have h16 : Entails.eval a c382 := h 381 (by decide)
  have h17 : Entails.eval a c1711 := derived1711 a h
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c364 := h 363 (by decide)
  have h20 : Entails.eval a c80 := h 79 (by decide)
  have h21 : Entails.eval a c239 := h 238 (by decide)
  have h22 : Entails.eval a c193 := h 192 (by decide)
  have h23 : Entails.eval a c754 := derived754 a h
  have h24 : Entails.eval a c259 := h 258 (by decide)
  have h25 : Entails.eval a c116 := h 115 (by decide)
  have h26 : Entails.eval a c1684 := derived1684 a h
  have h27 : Entails.eval a c118 := h 117 (by decide)
  have h28 : Entails.eval a c714 := derived714 a h
  have h29 : Entails.eval a c324 := h 323 (by decide)
  have h30 : Entails.eval a c289 := h 288 (by decide)
  have h31 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1836 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨45, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨43, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1684, some c1422, some c143, some c210, some c55, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1836 : lratChecker f1836 p1836 = .success := by decide +kernel
theorem unsat1836 : Unsatisfiable (PosFin 57) f1836 := by
  apply lratCheckerSound f1836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1836
  · intro a ha; simp [p1836] at ha; subst a; trivial
  · exact checked1836
theorem derived1836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1836 := by
  apply localUnsat_implies_entails f1836 [c1684, c1422, c143, c210, c55] c1836 unsat1836 (by rfl) a
  have h0 : Entails.eval a c1684 := derived1684 a h
  have h1 : Entails.eval a c1422 := derived1422 a h
  have h2 : Entails.eval a c143 := h 142 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1837 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, true), (⟨45, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c34, some c30, some c23, some c10, some c1836, some c116, some c1821, some c227, some c226, some c71, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1837 : lratChecker f1837 p1837 = .success := by decide +kernel
theorem unsat1837 : Unsatisfiable (PosFin 57) f1837 := by
  apply lratCheckerSound f1837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1837
  · intro a ha; simp [p1837] at ha; subst a; trivial
  · exact checked1837
theorem derived1837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1837 := by
  apply localUnsat_implies_entails f1837 [c1668, c1817, c112, c34, c30, c23, c10, c1836, c116, c1821, c227, c226, c71] c1837 unsat1837 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1836 := derived1836 a h
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c1821 := derived1821 a h
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1838 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c30, some c10, some c35, some c15, some c116, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1838 : lratChecker f1838 p1838 = .success := by decide +kernel
theorem unsat1838 : Unsatisfiable (PosFin 57) f1838 := by
  apply lratCheckerSound f1838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1838
  · intro a ha; simp [p1838] at ha; subst a; trivial
  · exact checked1838
theorem derived1838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1838 := by
  apply localUnsat_implies_entails f1838 [c1668, c30, c10, c35, c15, c116] c1838 unsat1838 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1839 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c1838, some c30, some c23, some c10, some c3, some c1819, some c1826, some c1823, some c93, some c190, some c116, some c379, some c188, some c14, some c95, some c184, some c1231, some c1825, some c884, some c1233, some c71, some c69, some c22, some c225, some c118, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1839 : lratChecker f1839 p1839 = .success := by decide +kernel
theorem unsat1839 : Unsatisfiable (PosFin 57) f1839 := by
  apply lratCheckerSound f1839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1839
  · intro a ha; simp [p1839] at ha; subst a; trivial
  · exact checked1839
theorem derived1839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1839 := by
  apply localUnsat_implies_entails f1839 [c1817, c1668, c112, c1838, c30, c23, c10, c3, c1819, c1826, c1823, c93, c190, c116, c379, c188, c14, c95, c184, c1231, c1825, c884, c1233, c71, c69, c22, c225, c118] c1839 unsat1839 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1838 := derived1838 a h
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1819 := derived1819 a h
  have h9 : Entails.eval a c1826 := derived1826 a h
  have h10 : Entails.eval a c1823 := derived1823 a h
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c1231 := derived1231 a h
  have h20 : Entails.eval a c1825 := derived1825 a h
  have h21 : Entails.eval a c884 := derived884 a h
  have h22 : Entails.eval a c1233 := derived1233 a h
  have h23 : Entails.eval a c71 := h 70 (by decide)
  have h24 : Entails.eval a c69 := h 68 (by decide)
  have h25 : Entails.eval a c22 := h 21 (by decide)
  have h26 : Entails.eval a c225 := h 224 (by decide)
  have h27 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1840 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c30, some c1839, some c113, some c189, some c1838, some c23, some c1834, some c1835, some c1832, some c161, some c374, some c1837, some c83, some c193, some c1113, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1840 : lratChecker f1840 p1840 = .success := by decide +kernel
theorem unsat1840 : Unsatisfiable (PosFin 57) f1840 := by
  apply lratCheckerSound f1840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1840
  · intro a ha; simp [p1840] at ha; subst a; trivial
  · exact checked1840
theorem derived1840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1840 := by
  apply localUnsat_implies_entails f1840 [c1668, c1817, c112, c10, c30, c1839, c113, c189, c1838, c23, c1834, c1835, c1832, c161, c374, c1837, c83, c193, c1113] c1840 unsat1840 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1839 := derived1839 a h
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c1838 := derived1838 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c1834 := derived1834 a h
  have h11 : Entails.eval a c1835 := derived1835 a h
  have h12 : Entails.eval a c1832 := derived1832 a h
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c1837 := derived1837 a h
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c1113 := derived1113 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1841 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨45, by decide⟩, true), (⟨49, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c861, some c114, some c238, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1841 : lratChecker f1841 p1841 = .success := by decide +kernel
theorem unsat1841 : Unsatisfiable (PosFin 57) f1841 := by
  apply lratCheckerSound f1841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1841
  · intro a ha; simp [p1841] at ha; subst a; trivial
  · exact checked1841
theorem derived1841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1841 := by
  apply localUnsat_implies_entails f1841 [c1668, c861, c114, c238] c1841 unsat1841 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c861 := derived861 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1842 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, true), (⟨45, by decide⟩, true), (⟨50, by decide⟩, false), (⟨41, by decide⟩, false), (⟨21, by decide⟩, true), (⟨43, by decide⟩, false), (⟨55, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1711, some c370, some c238, some c363, some c247, some c754, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1842 : lratChecker f1842 p1842 = .success := by decide +kernel
theorem unsat1842 : Unsatisfiable (PosFin 57) f1842 := by
  apply lratCheckerSound f1842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1842
  · intro a ha; simp [p1842] at ha; subst a; trivial
  · exact checked1842
theorem derived1842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1842 := by
  apply localUnsat_implies_entails f1842 [c1711, c370, c238, c363, c247, c754] c1842 unsat1842 (by rfl) a
  have h0 : Entails.eval a c1711 := derived1711 a h
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c754 := derived754 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1843 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c3, some c23, some c30, some c1838, some c1839, some c189, some c113, some c1840, some c73, some c93, some c161, some c379, some c184, some c1841, some c188, some c14, some c1231, some c1842, some c239, some c364, some c1831, some c466, some c258, some c259, some c754, some c1684, some c238, some c714, some c118, some c324, some c289, some c200, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1843 : lratChecker f1843 p1843 = .success := by decide +kernel
theorem unsat1843 : Unsatisfiable (PosFin 57) f1843 := by
  apply lratCheckerSound f1843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1843
  · intro a ha; simp [p1843] at ha; subst a; trivial
  · exact checked1843
theorem derived1843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1843 := by
  apply localUnsat_implies_entails f1843 [c1668, c1817, c112, c10, c3, c23, c30, c1838, c1839, c189, c113, c1840, c73, c93, c161, c379, c184, c1841, c188, c14, c1231, c1842, c239, c364, c1831, c466, c258, c259, c754, c1684, c238, c714, c118, c324, c289, c200] c1843 unsat1843 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1838 := derived1838 a h
  have h8 : Entails.eval a c1839 := derived1839 a h
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c1840 := derived1840 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c379 := h 378 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c1841 := derived1841 a h
  have h18 : Entails.eval a c188 := h 187 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c1231 := derived1231 a h
  have h21 : Entails.eval a c1842 := derived1842 a h
  have h22 : Entails.eval a c239 := h 238 (by decide)
  have h23 : Entails.eval a c364 := h 363 (by decide)
  have h24 : Entails.eval a c1831 := derived1831 a h
  have h25 : Entails.eval a c466 := derived466 a h
  have h26 : Entails.eval a c258 := h 257 (by decide)
  have h27 : Entails.eval a c259 := h 258 (by decide)
  have h28 : Entails.eval a c754 := derived754 a h
  have h29 : Entails.eval a c1684 := derived1684 a h
  have h30 : Entails.eval a c238 := h 237 (by decide)
  have h31 : Entails.eval a c714 := derived714 a h
  have h32 : Entails.eval a c118 := h 117 (by decide)
  have h33 : Entails.eval a c324 := h 323 (by decide)
  have h34 : Entails.eval a c289 := h 288 (by decide)
  have h35 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1844 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨10, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c167, some c372, some c186, some c363, some c382, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1844 : lratChecker f1844 p1844 = .success := by decide +kernel
theorem unsat1844 : Unsatisfiable (PosFin 57) f1844 := by
  apply lratCheckerSound f1844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1844
  · intro a ha; simp [p1844] at ha; subst a; trivial
  · exact checked1844
theorem derived1844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1844 := by
  apply localUnsat_implies_entails f1844 [c367, c167, c372, c186, c363, c382] c1844 unsat1844 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1845 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1843, some c112, some c10, some c3, some c191, some c1819, some c21, some c29, some c163, some c245, some c360, some c2, some c1844, some c1231, some c187, some c382, some c185, some c363, some c166, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1845 : lratChecker f1845 p1845 = .success := by decide +kernel
theorem unsat1845 : Unsatisfiable (PosFin 57) f1845 := by
  apply lratCheckerSound f1845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1845
  · intro a ha; simp [p1845] at ha; subst a; trivial
  · exact checked1845
theorem derived1845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1845 := by
  apply localUnsat_implies_entails f1845 [c1817, c1668, c1843, c112, c10, c3, c191, c1819, c21, c29, c163, c245, c360, c2, c1844, c1231, c187, c382, c185, c363, c166] c1845 unsat1845 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1843 := derived1843 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c1819 := derived1819 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c1844 := derived1844 a h
  have h15 : Entails.eval a c1231 := derived1231 a h
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c382 := h 381 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c363 := h 362 (by decide)
  have h20 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1846 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨45, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c1827, some c237, some c249, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1846 : lratChecker f1846 p1846 = .success := by decide +kernel
theorem unsat1846 : Unsatisfiable (PosFin 57) f1846 := by
  apply lratCheckerSound f1846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1846
  · intro a ha; simp [p1846] at ha; subst a; trivial
  · exact checked1846
theorem derived1846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1846 := by
  apply localUnsat_implies_entails f1846 [c374, c1827, c237, c249] c1846 unsat1846 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c1827 := derived1827 a h
  have h2 : Entails.eval a c237 := h 236 (by decide)
  have h3 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1847 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨19, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c74, some c245, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1847 : lratChecker f1847 p1847 = .success := by decide +kernel
theorem unsat1847 : Unsatisfiable (PosFin 57) f1847 := by
  apply lratCheckerSound f1847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1847
  · intro a ha; simp [p1847] at ha; subst a; trivial
  · exact checked1847
theorem derived1847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1847 := by
  apply localUnsat_implies_entails f1847 [c22, c74, c245] c1847 unsat1847 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1848 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨45, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c184, some c712, some c166, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1848 : lratChecker f1848 p1848 = .success := by decide +kernel
theorem unsat1848 : Unsatisfiable (PosFin 57) f1848 := by
  apply lratCheckerSound f1848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1848
  · intro a ha; simp [p1848] at ha; subst a; trivial
  · exact checked1848
theorem derived1848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1848 := by
  apply localUnsat_implies_entails f1848 [c1668, c184, c712, c166] c1848 unsat1848 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1849 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨42, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c1445, some c1848, some c249, some c237, some c166, some c1064, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1849 : lratChecker f1849 p1849 = .success := by decide +kernel
theorem unsat1849 : Unsatisfiable (PosFin 57) f1849 := by
  apply lratCheckerSound f1849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1849
  · intro a ha; simp [p1849] at ha; subst a; trivial
  · exact checked1849
theorem derived1849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1849 := by
  apply localUnsat_implies_entails f1849 [c188, c1445, c1848, c249, c237, c166, c1064] c1849 unsat1849 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c1445 := derived1445 a h
  have h2 : Entails.eval a c1848 := derived1848 a h
  have h3 : Entails.eval a c249 := h 248 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c1064 := derived1064 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1850 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c3, some c1843, some c1847, some c10, some c1845, some c1823, some c190, some c188, some c1231, some c1825, some c1692, some c1849, some c116, some c120, some c29, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1850 : lratChecker f1850 p1850 = .success := by decide +kernel
theorem unsat1850 : Unsatisfiable (PosFin 57) f1850 := by
  apply lratCheckerSound f1850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1850
  · intro a ha; simp [p1850] at ha; subst a; trivial
  · exact checked1850
theorem derived1850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1850 := by
  apply localUnsat_implies_entails f1850 [c1817, c1668, c112, c3, c1843, c1847, c10, c1845, c1823, c190, c188, c1231, c1825, c1692, c1849, c116, c120, c29] c1850 unsat1850 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1843 := derived1843 a h
  have h5 : Entails.eval a c1847 := derived1847 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c1845 := derived1845 a h
  have h8 : Entails.eval a c1823 := derived1823 a h
  have h9 : Entails.eval a c190 := h 189 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c1231 := derived1231 a h
  have h12 : Entails.eval a c1825 := derived1825 a h
  have h13 : Entails.eval a c1692 := derived1692 a h
  have h14 : Entails.eval a c1849 := derived1849 a h
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1851 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨56, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1231, some c188, some c1830, some c1841, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1851 : lratChecker f1851 p1851 = .success := by decide +kernel
theorem unsat1851 : Unsatisfiable (PosFin 57) f1851 := by
  apply lratCheckerSound f1851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1851
  · intro a ha; simp [p1851] at ha; subst a; trivial
  · exact checked1851
theorem derived1851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1851 := by
  apply localUnsat_implies_entails f1851 [c1668, c1231, c188, c1830, c1841] c1851 unsat1851 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c1830 := derived1830 a h
  have h4 : Entails.eval a c1841 := derived1841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1852 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨52, by decide⟩, true), (⟨13, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c655, some c1827, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1852 : lratChecker f1852 p1852 = .success := by decide +kernel
theorem unsat1852 : Unsatisfiable (PosFin 57) f1852 := by
  apply lratCheckerSound f1852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1852
  · intro a ha; simp [p1852] at ha; subst a; trivial
  · exact checked1852
theorem derived1852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1852 := by
  apply localUnsat_implies_entails f1852 [c1668, c655, c1827] c1852 unsat1852 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c1827 := derived1827 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1853 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c1841, some c238, some c1711, some c372, some c1731, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1853 : lratChecker f1853 p1853 = .success := by decide +kernel
theorem unsat1853 : Unsatisfiable (PosFin 57) f1853 := by
  apply lratCheckerSound f1853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1853
  · intro a ha; simp [p1853] at ha; subst a; trivial
  · exact checked1853
theorem derived1853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1853 := by
  apply localUnsat_implies_entails f1853 [c114, c1841, c238, c1711, c372, c1731] c1853 unsat1853 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c1841 := derived1841 a h
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c1711 := derived1711 a h
  have h4 : Entails.eval a c372 := h 371 (by decide)
  have h5 : Entails.eval a c1731 := derived1731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1854 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, true), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c238, some c1711, some c372, some c1731, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1854 : lratChecker f1854 p1854 = .success := by decide +kernel
theorem unsat1854 : Unsatisfiable (PosFin 57) f1854 := by
  apply lratCheckerSound f1854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1854
  · intro a ha; simp [p1854] at ha; subst a; trivial
  · exact checked1854
theorem derived1854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1854 := by
  apply localUnsat_implies_entails f1854 [c1832, c238, c1711, c372, c1731] c1854 unsat1854 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c238 := h 237 (by decide)
  have h2 : Entails.eval a c1711 := derived1711 a h
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c1731 := derived1731 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1855 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨52, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c239, some c372, some c258, some c238, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1855 : lratChecker f1855 p1855 = .success := by decide +kernel
theorem unsat1855 : Unsatisfiable (PosFin 57) f1855 := by
  apply lratCheckerSound f1855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1855
  · intro a ha; simp [p1855] at ha; subst a; trivial
  · exact checked1855
theorem derived1855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1855 := by
  apply localUnsat_implies_entails f1855 [c364, c239, c372, c258, c238] c1855 unsat1855 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1856 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c189, some c3, some c1847, some c2, some c379, some c245, some c29, some c113, some c1852, some c1851, some c1853, some c14, some c1854, some c73, some c1855, some c164, some c15, some c1684, some c1426, some c143, some c142, some c55, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1856 : lratChecker f1856 p1856 = .success := by decide +kernel
theorem unsat1856 : Unsatisfiable (PosFin 57) f1856 := by
  apply lratCheckerSound f1856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1856
  · intro a ha; simp [p1856] at ha; subst a; trivial
  · exact checked1856
theorem derived1856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1856 := by
  apply localUnsat_implies_entails f1856 [c1668, c10, c189, c3, c1847, c2, c379, c245, c29, c113, c1852, c1851, c1853, c14, c1854, c73, c1855, c164, c15, c1684, c1426, c143, c142, c55] c1856 unsat1856 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1847 := derived1847 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c1852 := derived1852 a h
  have h11 : Entails.eval a c1851 := derived1851 a h
  have h12 : Entails.eval a c1853 := derived1853 a h
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c1854 := derived1854 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c1855 := derived1855 a h
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c1684 := derived1684 a h
  have h20 : Entails.eval a c1426 := derived1426 a h
  have h21 : Entails.eval a c143 := h 142 (by decide)
  have h22 : Entails.eval a c142 := h 141 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1857 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c113, some c189, some c3, some c1851, some c161, some c655, some c73, some c1833, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1857 : lratChecker f1857 p1857 = .success := by decide +kernel
theorem unsat1857 : Unsatisfiable (PosFin 57) f1857 := by
  apply lratCheckerSound f1857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1857
  · intro a ha; simp [p1857] at ha; subst a; trivial
  · exact checked1857
theorem derived1857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1857 := by
  apply localUnsat_implies_entails f1857 [c1668, c10, c113, c189, c3, c1851, c161, c655, c73, c1833] c1857 unsat1857 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c1851 := derived1851 a h
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c1833 := derived1833 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1858 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1854, some c382, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1858 : lratChecker f1858 p1858 = .success := by decide +kernel
theorem unsat1858 : Unsatisfiable (PosFin 57) f1858 := by
  apply lratCheckerSound f1858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1858
  · intro a ha; simp [p1858] at ha; subst a; trivial
  · exact checked1858
theorem derived1858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1858 := by
  apply localUnsat_implies_entails f1858 [c1829, c1854, c382] c1858 unsat1858 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1854 := derived1854 a h
  have h2 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1859 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨56, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1858, some c73, some c93, some c379, some c184, some c1855, some c166, some c370, some c363, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1859 : lratChecker f1859 p1859 = .success := by decide +kernel
theorem unsat1859 : Unsatisfiable (PosFin 57) f1859 := by
  apply lratCheckerSound f1859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1859
  · intro a ha; simp [p1859] at ha; subst a; trivial
  · exact checked1859
theorem derived1859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1859 := by
  apply localUnsat_implies_entails f1859 [c1668, c1858, c73, c93, c379, c184, c1855, c166, c370, c363] c1859 unsat1859 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1858 := derived1858 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c1855 := derived1855 a h
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1860 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c1843, some c1850, some c1856, some c1254, some c10, some c189, some c3, some c1847, some c113, some c1857, some c1859, some c161, some c1848, some c655, some c73, some c249, some c374, some c1832, some c1158, some c1470, some c259, some c1113, some c1846, some c193, some c1711, some c1692, some c15, some c1684, some c325, some c529, some c226, some c71, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1860 : lratChecker f1860 p1860 = .success := by decide +kernel
theorem unsat1860 : Unsatisfiable (PosFin 57) f1860 := by
  apply lratCheckerSound f1860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1860
  · intro a ha; simp [p1860] at ha; subst a; trivial
  · exact checked1860
theorem derived1860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1860 := by
  apply localUnsat_implies_entails f1860 [c1668, c1817, c112, c1843, c1850, c1856, c1254, c10, c189, c3, c1847, c113, c1857, c1859, c161, c1848, c655, c73, c249, c374, c1832, c1158, c1470, c259, c1113, c1846, c193, c1711, c1692, c15, c1684, c325, c529, c226, c71] c1860 unsat1860 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c1843 := derived1843 a h
  have h4 : Entails.eval a c1850 := derived1850 a h
  have h5 : Entails.eval a c1856 := derived1856 a h
  have h6 : Entails.eval a c1254 := derived1254 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1847 := derived1847 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c1857 := derived1857 a h
  have h13 : Entails.eval a c1859 := derived1859 a h
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c1848 := derived1848 a h
  have h16 : Entails.eval a c655 := derived655 a h
  have h17 : Entails.eval a c73 := h 72 (by decide)
  have h18 : Entails.eval a c249 := h 248 (by decide)
  have h19 : Entails.eval a c374 := h 373 (by decide)
  have h20 : Entails.eval a c1832 := derived1832 a h
  have h21 : Entails.eval a c1158 := derived1158 a h
  have h22 : Entails.eval a c1470 := derived1470 a h
  have h23 : Entails.eval a c259 := h 258 (by decide)
  have h24 : Entails.eval a c1113 := derived1113 a h
  have h25 : Entails.eval a c1846 := derived1846 a h
  have h26 : Entails.eval a c193 := h 192 (by decide)
  have h27 : Entails.eval a c1711 := derived1711 a h
  have h28 : Entails.eval a c1692 := derived1692 a h
  have h29 : Entails.eval a c15 := h 14 (by decide)
  have h30 : Entails.eval a c1684 := derived1684 a h
  have h31 : Entails.eval a c325 := h 324 (by decide)
  have h32 : Entails.eval a c529 := derived529 a h
  have h33 : Entails.eval a c226 := h 225 (by decide)
  have h34 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1861 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c193, some c167, some c184, some c365, some c382, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1861 : lratChecker f1861 p1861 = .success := by decide +kernel
theorem unsat1861 : Unsatisfiable (PosFin 57) f1861 := by
  apply lratCheckerSound f1861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1861
  · intro a ha; simp [p1861] at ha; subst a; trivial
  · exact checked1861
theorem derived1861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1861 := by
  apply localUnsat_implies_entails f1861 [c188, c193, c167, c184, c365, c382] c1861 unsat1861 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1862 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c166, some c363, some c364, some c370, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1862 : lratChecker f1862 p1862 = .success := by decide +kernel
theorem unsat1862 : Unsatisfiable (PosFin 57) f1862 := by
  apply lratCheckerSound f1862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1862
  · intro a ha; simp [p1862] at ha; subst a; trivial
  · exact checked1862
theorem derived1862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1862 := by
  apply localUnsat_implies_entails f1862 [c184, c166, c363, c364, c370] c1862 unsat1862 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1863 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨8, by decide⟩, false), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨16, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨42, by decide⟩, false), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1254, some c240, some c236, some c1005, some c166, some c1684, some c677, some c340, some c72, some c157, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1863 : lratChecker f1863 p1863 = .success := by decide +kernel
theorem unsat1863 : Unsatisfiable (PosFin 57) f1863 := by
  apply lratCheckerSound f1863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1863
  · intro a ha; simp [p1863] at ha; subst a; trivial
  · exact checked1863
theorem derived1863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1863 := by
  apply localUnsat_implies_entails f1863 [c1668, c1817, c1254, c240, c236, c1005, c166, c1684, c677, c340, c72, c157] c1863 unsat1863 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c1005 := derived1005 a h
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c1684 := derived1684 a h
  have h8 : Entails.eval a c677 := derived677 a h
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1864 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c3, some c1843, some c1847, some c1850, some c189, some c1856, some c1254, some c1860, some c21, some c29, some c161, some c245, some c260, some c31, some c1861, some c1231, some c1862, some c382, some c366, some c942, some c1711, some c370, some c15, some c1863, some c264, some c1113, some c238, some c193, some c262, some c1684, some c340, some c219, some c225, some c319, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked1864 : lratChecker f1864 p1864 = .success := by decide +kernel
theorem unsat1864 : Unsatisfiable (PosFin 57) f1864 := by
  apply lratCheckerSound f1864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1864
  · intro a ha; simp [p1864] at ha; subst a; trivial
  · exact checked1864
theorem derived1864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1864 := by
  apply localUnsat_implies_entails f1864 [c1668, c1817, c112, c10, c3, c1843, c1847, c1850, c189, c1856, c1254, c1860, c21, c29, c161, c245, c260, c31, c1861, c1231, c1862, c382, c366, c942, c1711, c370, c15, c1863, c264, c1113, c238, c193, c262, c1684, c340, c219, c225, c319] c1864 unsat1864 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c1843 := derived1843 a h
  have h6 : Entails.eval a c1847 := derived1847 a h
  have h7 : Entails.eval a c1850 := derived1850 a h
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c1856 := derived1856 a h
  have h10 : Entails.eval a c1254 := derived1254 a h
  have h11 : Entails.eval a c1860 := derived1860 a h
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c245 := h 244 (by decide)
  have h16 : Entails.eval a c260 := h 259 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c1861 := derived1861 a h
  have h19 : Entails.eval a c1231 := derived1231 a h
  have h20 : Entails.eval a c1862 := derived1862 a h
  have h21 : Entails.eval a c382 := h 381 (by decide)
  have h22 : Entails.eval a c366 := h 365 (by decide)
  have h23 : Entails.eval a c942 := derived942 a h
  have h24 : Entails.eval a c1711 := derived1711 a h
  have h25 : Entails.eval a c370 := h 369 (by decide)
  have h26 : Entails.eval a c15 := h 14 (by decide)
  have h27 : Entails.eval a c1863 := derived1863 a h
  have h28 : Entails.eval a c264 := h 263 (by decide)
  have h29 : Entails.eval a c1113 := derived1113 a h
  have h30 : Entails.eval a c238 := h 237 (by decide)
  have h31 : Entails.eval a c193 := h 192 (by decide)
  have h32 : Entails.eval a c262 := h 261 (by decide)
  have h33 : Entails.eval a c1684 := derived1684 a h
  have h34 : Entails.eval a c340 := h 339 (by decide)
  have h35 : Entails.eval a c219 := h 218 (by decide)
  have h36 : Entails.eval a c225 := h 224 (by decide)
  have h37 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1865 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨45, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c30, some c1003, some c113, some c3, some c383, some c1829, some c1841, some c14, some c93, some c1838, some c1630, some c1711, some c239, some c466, some c256, some c248, some c1684, some c1262, some c336, some c221, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1865 : lratChecker f1865 p1865 = .success := by decide +kernel
theorem unsat1865 : Unsatisfiable (PosFin 57) f1865 := by
  apply lratCheckerSound f1865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1865
  · intro a ha; simp [p1865] at ha; subst a; trivial
  · exact checked1865
theorem derived1865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1865 := by
  apply localUnsat_implies_entails f1865 [c1668, c10, c30, c1003, c113, c3, c383, c1829, c1841, c14, c93, c1838, c1630, c1711, c239, c466, c256, c248, c1684, c1262, c336, c221] c1865 unsat1865 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c1003 := derived1003 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c1829 := derived1829 a h
  have h8 : Entails.eval a c1841 := derived1841 a h
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c1838 := derived1838 a h
  have h12 : Entails.eval a c1630 := derived1630 a h
  have h13 : Entails.eval a c1711 := derived1711 a h
  have h14 : Entails.eval a c239 := h 238 (by decide)
  have h15 : Entails.eval a c466 := derived466 a h
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c1684 := derived1684 a h
  have h19 : Entails.eval a c1262 := derived1262 a h
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1866 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨19, by decide⟩, true), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c1003, some c30, some c113, some c1838, some c3, some c383, some c1829, some c73, some c93, some c1841, some c14, some c1865, some c366, some c1711, some c164, some c365, some c238, some c1684, some c247, some c336, some c22, some c198, some c297, some c284, some c143, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1866 : lratChecker f1866 p1866 = .success := by decide +kernel
theorem unsat1866 : Unsatisfiable (PosFin 57) f1866 := by
  apply lratCheckerSound f1866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1866
  · intro a ha; simp [p1866] at ha; subst a; trivial
  · exact checked1866
theorem derived1866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1866 := by
  apply localUnsat_implies_entails f1866 [c1668, c10, c1003, c30, c113, c1838, c3, c383, c1829, c73, c93, c1841, c14, c1865, c366, c1711, c164, c365, c238, c1684, c247, c336, c22, c198, c297, c284, c143] c1866 unsat1866 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c1838 := derived1838 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c1829 := derived1829 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c1841 := derived1841 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c1865 := derived1865 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c1711 := derived1711 a h
  have h16 : Entails.eval a c164 := h 163 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c238 := h 237 (by decide)
  have h19 : Entails.eval a c1684 := derived1684 a h
  have h20 : Entails.eval a c247 := h 246 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  have h22 : Entails.eval a c22 := h 21 (by decide)
  have h23 : Entails.eval a c198 := h 197 (by decide)
  have h24 : Entails.eval a c297 := h 296 (by decide)
  have h25 : Entails.eval a c284 := h 283 (by decide)
  have h26 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1867 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c23, some c1864, some c1866, some c30, some c1003, some c10, some c161, some c73, some c243, some c1158, some c81, some c375, some c113, some c1838, some c189, some c1711, some c1004, some c240, some c14, some c258, some c261, some c1821, some c227, some c220, some c323, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1867 : lratChecker f1867 p1867 = .success := by decide +kernel
theorem unsat1867 : Unsatisfiable (PosFin 57) f1867 := by
  apply lratCheckerSound f1867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1867
  · intro a ha; simp [p1867] at ha; subst a; trivial
  · exact checked1867
theorem derived1867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1867 := by
  apply localUnsat_implies_entails f1867 [c1817, c1668, c112, c23, c1864, c1866, c30, c1003, c10, c161, c73, c243, c1158, c81, c375, c113, c1838, c189, c1711, c1004, c240, c14, c258, c261, c1821, c227, c220, c323] c1867 unsat1867 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c1864 := derived1864 a h
  have h5 : Entails.eval a c1866 := derived1866 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1003 := derived1003 a h
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c1158 := derived1158 a h
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c1838 := derived1838 a h
  have h17 : Entails.eval a c189 := h 188 (by decide)
  have h18 : Entails.eval a c1711 := derived1711 a h
  have h19 : Entails.eval a c1004 := derived1004 a h
  have h20 : Entails.eval a c240 := h 239 (by decide)
  have h21 : Entails.eval a c14 := h 13 (by decide)
  have h22 : Entails.eval a c258 := h 257 (by decide)
  have h23 : Entails.eval a c261 := h 260 (by decide)
  have h24 : Entails.eval a c1821 := derived1821 a h
  have h25 : Entails.eval a c227 := h 226 (by decide)
  have h26 : Entails.eval a c220 := h 219 (by decide)
  have h27 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1868 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c112, some c10, some c1864, some c1003, some c189, some c3, some c23, some c30, some c1838, some c113, some c1866, some c161, some c374, some c73, some c83, some c378, some c1113, some c1867, some c364, some c379, some c2, some c1254, some c193, some c1837, some c258, some c1821, some c201, some c227, some c54, some c72, some c135, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1868 : lratChecker f1868 p1868 = .success := by decide +kernel
theorem unsat1868 : Unsatisfiable (PosFin 57) f1868 := by
  apply lratCheckerSound f1868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1868
  · intro a ha; simp [p1868] at ha; subst a; trivial
  · exact checked1868
theorem derived1868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1868 := by
  apply localUnsat_implies_entails f1868 [c1668, c1817, c112, c10, c1864, c1003, c189, c3, c23, c30, c1838, c113, c1866, c161, c374, c73, c83, c378, c1113, c1867, c364, c379, c2, c1254, c193, c1837, c258, c1821, c201, c227, c54, c72, c135] c1868 unsat1868 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1864 := derived1864 a h
  have h5 : Entails.eval a c1003 := derived1003 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c1838 := derived1838 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c1866 := derived1866 a h
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c378 := h 377 (by decide)
  have h18 : Entails.eval a c1113 := derived1113 a h
  have h19 : Entails.eval a c1867 := derived1867 a h
  have h20 : Entails.eval a c364 := h 363 (by decide)
  have h21 : Entails.eval a c379 := h 378 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  have h23 : Entails.eval a c1254 := derived1254 a h
  have h24 : Entails.eval a c193 := h 192 (by decide)
  have h25 : Entails.eval a c1837 := derived1837 a h
  have h26 : Entails.eval a c258 := h 257 (by decide)
  have h27 : Entails.eval a c1821 := derived1821 a h
  have h28 : Entails.eval a c201 := h 200 (by decide)
  have h29 : Entails.eval a c227 := h 226 (by decide)
  have h30 : Entails.eval a c54 := h 53 (by decide)
  have h31 : Entails.eval a c72 := h 71 (by decide)
  have h32 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1869 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨18, by decide⟩, true), (⟨45, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, true), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c1003, some c113, some c3, some c383, some c1829, some c1841, some c14, some c93, some c1630, some c609, some c1711, some c239, some c116, some c15, some c1684, some c143, some c1461, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1869 : lratChecker f1869 p1869 = .success := by decide +kernel
theorem unsat1869 : Unsatisfiable (PosFin 57) f1869 := by
  apply lratCheckerSound f1869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1869
  · intro a ha; simp [p1869] at ha; subst a; trivial
  · exact checked1869
theorem derived1869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1869 := by
  apply localUnsat_implies_entails f1869 [c1668, c10, c1003, c113, c3, c383, c1829, c1841, c14, c93, c1630, c609, c1711, c239, c116, c15, c1684, c143, c1461] c1869 unsat1869 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c1829 := derived1829 a h
  have h7 : Entails.eval a c1841 := derived1841 a h
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c1630 := derived1630 a h
  have h11 : Entails.eval a c609 := derived609 a h
  have h12 : Entails.eval a c1711 := derived1711 a h
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c1684 := derived1684 a h
  have h17 : Entails.eval a c143 := h 142 (by decide)
  have h18 : Entails.eval a c1461 := derived1461 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1870 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c10, some c1003, some c113, some c3, some c251, some c383, some c1829, some c73, some c93, some c1841, some c245, some c14, some c1869, some c366, some c164, some c15, some c1684, some c336, some c342, some c221, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1870 : lratChecker f1870 p1870 = .success := by decide +kernel
theorem unsat1870 : Unsatisfiable (PosFin 57) f1870 := by
  apply lratCheckerSound f1870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1870
  · intro a ha; simp [p1870] at ha; subst a; trivial
  · exact checked1870
theorem derived1870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1870 := by
  apply localUnsat_implies_entails f1870 [c1668, c10, c1003, c113, c3, c251, c383, c1829, c73, c93, c1841, c245, c14, c1869, c366, c164, c15, c1684, c336, c342, c221] c1870 unsat1870 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c1829 := derived1829 a h
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c1841 := derived1841 a h
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c1869 := derived1869 a h
  have h14 : Entails.eval a c366 := h 365 (by decide)
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c1684 := derived1684 a h
  have h18 : Entails.eval a c336 := h 335 (by decide)
  have h19 : Entails.eval a c342 := h 341 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1871 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c336, some c342, some c153, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p1871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1871 : lratChecker f1871 p1871 = .success := by decide +kernel
theorem unsat1871 : Unsatisfiable (PosFin 57) f1871 := by
  apply lratCheckerSound f1871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1871
  · intro a ha; simp [p1871] at ha; subst a; trivial
  · exact checked1871
theorem derived1871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1871 := by
  apply localUnsat_implies_entails f1871 [c336, c342, c153] c1871 unsat1871 (by rfl) a
  have h0 : Entails.eval a c336 := h 335 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1872 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1871, some c131, some c297, some c303, some c141, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1872 : lratChecker f1872 p1872 = .success := by decide +kernel
theorem unsat1872 : Unsatisfiable (PosFin 57) f1872 := by
  apply lratCheckerSound f1872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1872
  · intro a ha; simp [p1872] at ha; subst a; trivial
  · exact checked1872
theorem derived1872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1872 := by
  apply localUnsat_implies_entails f1872 [c1871, c131, c297, c303, c141] c1872 unsat1872 (by rfl) a
  have h0 : Entails.eval a c1871 := derived1871 a h
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c297 := h 296 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1873 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨52, by decide⟩, true), (⟨18, by decide⟩, true), (⟨45, by decide⟩, false), (⟨21, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c14, some c1003, some c10, some c161, some c73, some c378, some c655, some c189, some c3, some c1872, some c1233, some c15, some c1684, some c336, some c325, some c220, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1873 : lratChecker f1873 p1873 = .success := by decide +kernel
theorem unsat1873 : Unsatisfiable (PosFin 57) f1873 := by
  apply lratCheckerSound f1873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1873
  · intro a ha; simp [p1873] at ha; subst a; trivial
  · exact checked1873
theorem derived1873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1873 := by
  apply localUnsat_implies_entails f1873 [c1668, c14, c1003, c10, c161, c73, c378, c655, c189, c3, c1872, c1233, c15, c1684, c336, c325, c220] c1873 unsat1873 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c1003 := derived1003 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c1872 := derived1872 a h
  have h11 : Entails.eval a c1233 := derived1233 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c1684 := derived1684 a h
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1874 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c3, some c1847, some c251, some c1003, some c10, some c113, some c1870, some c161, some c655, some c374, some c73, some c1158, some c378, some c260, some c249, some c364, some c1711, some c1004, some c14, some c1873, some c2, some c1233, some c15, some c1684, some c325, some c320, some c220, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1874 : lratChecker f1874 p1874 = .success := by decide +kernel
theorem unsat1874 : Unsatisfiable (PosFin 57) f1874 := by
  apply lratCheckerSound f1874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1874
  · intro a ha; simp [p1874] at ha; subst a; trivial
  · exact checked1874
theorem derived1874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1874 := by
  apply localUnsat_implies_entails f1874 [c1668, c3, c1847, c251, c1003, c10, c113, c1870, c161, c655, c374, c73, c1158, c378, c260, c249, c364, c1711, c1004, c14, c1873, c2, c1233, c15, c1684, c325, c320, c220] c1874 unsat1874 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1847 := derived1847 a h
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c1003 := derived1003 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c1870 := derived1870 a h
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c655 := derived655 a h
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c1158 := derived1158 a h
  have h13 : Entails.eval a c378 := h 377 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c249 := h 248 (by decide)
  have h16 : Entails.eval a c364 := h 363 (by decide)
  have h17 : Entails.eval a c1711 := derived1711 a h
  have h18 : Entails.eval a c1004 := derived1004 a h
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c1873 := derived1873 a h
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c1233 := derived1233 a h
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c1684 := derived1684 a h
  have h25 : Entails.eval a c325 := h 324 (by decide)
  have h26 : Entails.eval a c320 := h 319 (by decide)
  have h27 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1875 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c3, some c10, some c1864, some c1003, some c383, some c189, some c1868, some c251, some c1847, some c1874, some c21, some c29, some c161, some c245, some c260, some c2, some c93, some c31, some c378, some c1714, some c942, some c1711, some c370, some c15, some c236, some c1863, some c166, some c185, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1875 : lratChecker f1875 p1875 = .success := by decide +kernel
theorem unsat1875 : Unsatisfiable (PosFin 57) f1875 := by
  apply lratCheckerSound f1875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1875
  · intro a ha; simp [p1875] at ha; subst a; trivial
  · exact checked1875
theorem derived1875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1875 := by
  apply localUnsat_implies_entails f1875 [c1817, c1668, c112, c3, c10, c1864, c1003, c383, c189, c1868, c251, c1847, c1874, c21, c29, c161, c245, c260, c2, c93, c31, c378, c1714, c942, c1711, c370, c15, c236, c1863, c166, c185] c1875 unsat1875 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c1864 := derived1864 a h
  have h6 : Entails.eval a c1003 := derived1003 a h
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c1868 := derived1868 a h
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c1847 := derived1847 a h
  have h12 : Entails.eval a c1874 := derived1874 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c161 := h 160 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c260 := h 259 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c93 := h 92 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c378 := h 377 (by decide)
  have h22 : Entails.eval a c1714 := derived1714 a h
  have h23 : Entails.eval a c942 := derived942 a h
  have h24 : Entails.eval a c1711 := derived1711 a h
  have h25 : Entails.eval a c370 := h 369 (by decide)
  have h26 : Entails.eval a c15 := h 14 (by decide)
  have h27 : Entails.eval a c236 := h 235 (by decide)
  have h28 : Entails.eval a c1863 := derived1863 a h
  have h29 : Entails.eval a c166 := h 165 (by decide)
  have h30 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1876 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c1231, some c1875, some c112, some c23, some c171, some c367, some c30, some c115, some c191, some c379, some c761, some c363, some c169, some c371, some c1102, some c862, some c81, some c1458, some c1254, some c162, some c35, some c969, some c55, some c134, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1876 : lratChecker f1876 p1876 = .success := by decide +kernel
theorem unsat1876 : Unsatisfiable (PosFin 57) f1876 := by
  apply lratCheckerSound f1876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1876
  · intro a ha; simp [p1876] at ha; subst a; trivial
  · exact checked1876
theorem derived1876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1876 := by
  apply localUnsat_implies_entails f1876 [c1817, c1668, c1231, c1875, c112, c23, c171, c367, c30, c115, c191, c379, c761, c363, c169, c371, c1102, c862, c81, c1458, c1254, c162, c35, c969, c55, c134] c1876 unsat1876 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c379 := h 378 (by decide)
  have h12 : Entails.eval a c761 := derived761 a h
  have h13 : Entails.eval a c363 := h 362 (by decide)
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c1102 := derived1102 a h
  have h17 : Entails.eval a c862 := derived862 a h
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c1458 := derived1458 a h
  have h20 : Entails.eval a c1254 := derived1254 a h
  have h21 : Entails.eval a c162 := h 161 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c969 := derived969 a h
  have h24 : Entails.eval a c55 := h 54 (by decide)
  have h25 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1877 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c2, some c165, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1877 : lratChecker f1877 p1877 = .success := by decide +kernel
theorem unsat1877 : Unsatisfiable (PosFin 57) f1877 := by
  apply lratCheckerSound f1877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1877
  · intro a ha; simp [p1877] at ha; subst a; trivial
  · exact checked1877
theorem derived1877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1877 := by
  apply localUnsat_implies_entails f1877 [c74, c2, c165] c1877 unsat1877 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1878 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1231, some c1875, some c112, some c23, some c1877, some c379, some c1876, some c188, some c184, some c190, some c192, some c169, some c808, some c854, some c363, some c336, some c70, some c199, some c135, some c287, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1878 : lratChecker f1878 p1878 = .success := by decide +kernel
theorem unsat1878 : Unsatisfiable (PosFin 57) f1878 := by
  apply lratCheckerSound f1878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1878
  · intro a ha; simp [p1878] at ha; subst a; trivial
  · exact checked1878
theorem derived1878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1878 := by
  apply localUnsat_implies_entails f1878 [c1668, c1817, c1231, c1875, c112, c23, c1877, c379, c1876, c188, c184, c190, c192, c169, c808, c854, c363, c336, c70, c199, c135, c287] c1878 unsat1878 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1875 := derived1875 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c1877 := derived1877 a h
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c1876 := derived1876 a h
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c808 := derived808 a h
  have h15 : Entails.eval a c854 := derived854 a h
  have h16 : Entails.eval a c363 := h 362 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c135 := h 134 (by decide)
  have h21 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1879 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨19, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c1668, some c112, some c30, some c1875, some c1878, some c196, some c113, some c1851, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1879 : lratChecker f1879 p1879 = .success := by decide +kernel
theorem unsat1879 : Unsatisfiable (PosFin 57) f1879 := by
  apply lratCheckerSound f1879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1879
  · intro a ha; simp [p1879] at ha; subst a; trivial
  · exact checked1879
theorem derived1879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1879 := by
  apply localUnsat_implies_entails f1879 [c1817, c1668, c112, c30, c1875, c1878, c196, c113, c1851] c1879 unsat1879 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c1668 := derived1668 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c1875 := derived1875 a h
  have h5 : Entails.eval a c1878 := derived1878 a h
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c1851 := derived1851 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1880 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c171, some c185, some c363, some c169, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1880 : lratChecker f1880 p1880 = .success := by decide +kernel
theorem unsat1880 : Unsatisfiable (PosFin 57) f1880 := by
  apply lratCheckerSound f1880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1880
  · intro a ha; simp [p1880] at ha; subst a; trivial
  · exact checked1880
theorem derived1880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1880 := by
  apply localUnsat_implies_entails f1880 [c191, c171, c185, c363, c169] c1880 unsat1880 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1881 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c1817, some c1875, some c112, some c23, some c1877, some c379, some c1879, some c1880, some c184, some c192, some c169, some c363, some c364, some c370, some c81, some c1390, some c195, some c808, some c199, some c336, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1881 : lratChecker f1881 p1881 = .success := by decide +kernel
theorem unsat1881 : Unsatisfiable (PosFin 57) f1881 := by
  apply lratCheckerSound f1881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1881
  · intro a ha; simp [p1881] at ha; subst a; trivial
  · exact checked1881
theorem derived1881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1881 := by
  apply localUnsat_implies_entails f1881 [c1668, c1817, c1875, c112, c23, c1877, c379, c1879, c1880, c184, c192, c169, c363, c364, c370, c81, c1390, c195, c808, c199, c336] c1881 unsat1881 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c1817 := derived1817 a h
  have h2 : Entails.eval a c1875 := derived1875 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c1877 := derived1877 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c1879 := derived1879 a h
  have h8 : Entails.eval a c1880 := derived1880 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c169 := h 168 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  have h14 : Entails.eval a c370 := h 369 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c1390 := derived1390 a h
  have h17 : Entails.eval a c195 := h 194 (by decide)
  have h18 : Entails.eval a c808 := derived808 a h
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1882 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨50, by decide⟩, false), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨56, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1817, some c854, some c703, some c70, some c300, some c203, some c147, some c54, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1882 : lratChecker f1882 p1882 = .success := by decide +kernel
theorem unsat1882 : Unsatisfiable (PosFin 57) f1882 := by
  apply lratCheckerSound f1882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1882
  · intro a ha; simp [p1882] at ha; subst a; trivial
  · exact checked1882
theorem derived1882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1882 := by
  apply localUnsat_implies_entails f1882 [c1817, c854, c703, c70, c300, c203, c147, c54] c1882 unsat1882 (by rfl) a
  have h0 : Entails.eval a c1817 := derived1817 a h
  have h1 : Entails.eval a c854 := derived854 a h
  have h2 : Entails.eval a c703 := derived703 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1883 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨54, by decide⟩, true), (⟨42, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1668, some c189, some c165, some c1844, some c82, some c163, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1883 : lratChecker f1883 p1883 = .success := by decide +kernel
theorem unsat1883 : Unsatisfiable (PosFin 57) f1883 := by
  apply lratCheckerSound f1883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1883
  · intro a ha; simp [p1883] at ha; subst a; trivial
  · exact checked1883
theorem derived1883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1883 := by
  apply localUnsat_implies_entails f1883 [c1668, c189, c165, c1844, c82, c163] c1883 unsat1883 (by rfl) a
  have h0 : Entails.eval a c1668 := derived1668 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c1844 := derived1844 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1883

end CochromaticTwenty.Certificates.B16_2_2
