import MerLeanExperiment.Certificates.B16_8_2.Steps1300_1399

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1781 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c2, some c1482, some c114, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1781 : lratChecker f1781 p1781 = .success := by decide +kernel
theorem unsat1781 : Unsatisfiable (PosFin 57) f1781 := by
  apply lratCheckerSound f1781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1781
  · intro a ha; simp [p1781] at ha; subst a; trivial
  · exact checked1781
theorem derived1781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1781 := by
  apply localUnsat_implies_entails f1781 [c1779, c2, c1482, c114] c1781 unsat1781 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c1482 := derived1482 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1782 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨54, by decide⟩, true), (⟨27, by decide⟩, false), (⟨56, by decide⟩, false), (⟨33, by decide⟩, true), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c841, some c244, some c209, some c240, some c254, some c255, some c1781, some c170, some c121, some c160, some c109, some c188, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1782 : lratChecker f1782 p1782 = .success := by decide +kernel
theorem unsat1782 : Unsatisfiable (PosFin 57) f1782 := by
  apply lratCheckerSound f1782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1782
  · intro a ha; simp [p1782] at ha; subst a; trivial
  · exact checked1782
theorem derived1782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1782 := by
  apply localUnsat_implies_entails f1782 [c293, c841, c244, c209, c240, c254, c255, c1781, c170, c121, c160, c109, c188] c1782 unsat1782 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c240 := h 239 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c1781 := derived1781 a h
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1783 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c123, some c174, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1783 : lratChecker f1783 p1783 = .success := by decide +kernel
theorem unsat1783 : Unsatisfiable (PosFin 57) f1783 := by
  apply lratCheckerSound f1783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1783
  · intro a ha; simp [p1783] at ha; subst a; trivial
  · exact checked1783
theorem derived1783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1783 := by
  apply localUnsat_implies_entails f1783 [c121, c123, c174] c1783 unsat1783 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1784 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨13, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨51, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c212, some c218, some c242, some c256, some c1480, some c174, some c111, some c147, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p1784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1784 : lratChecker f1784 p1784 = .success := by decide +kernel
theorem unsat1784 : Unsatisfiable (PosFin 57) f1784 := by
  apply lratCheckerSound f1784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1784
  · intro a ha; simp [p1784] at ha; subst a; trivial
  · exact checked1784
theorem derived1784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1784 := by
  apply localUnsat_implies_entails f1784 [c212, c218, c242, c256, c1480, c174, c111, c147] c1784 unsat1784 (by rfl) a
  have h0 : Entails.eval a c212 := h 211 (by decide)
  have h1 : Entails.eval a c218 := h 217 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c1480 := derived1480 a h
  have h5 : Entails.eval a c174 := h 173 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1785 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1671, some c39, some c45, some c310, some c309, some c40, some c49, some c328, some c347, some c103, some c72, some c79, some c47, some c841, some c1700, some c372, some c323, some c277, some c89, some c336, some c293, some c1780, some c1782, some c207, some c205, some c444, some c1781, some c1783, some c157, some c160, some c12, some c1784, some c146, some c126, some c176, some c1068, some c1223, some c223, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]]
theorem checked1785 : lratChecker f1785 p1785 = .success := by decide +kernel
theorem unsat1785 : Unsatisfiable (PosFin 57) f1785 := by
  apply lratCheckerSound f1785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1785
  · intro a ha; simp [p1785] at ha; subst a; trivial
  · exact checked1785
theorem derived1785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1785 := by
  apply localUnsat_implies_entails f1785 [c1779, c98, c1671, c39, c45, c310, c309, c40, c49, c328, c347, c103, c72, c79, c47, c841, c1700, c372, c323, c277, c89, c336, c293, c1780, c1782, c207, c205, c444, c1781, c1783, c157, c160, c12, c1784, c146, c126, c176, c1068, c1223, c223] c1785 unsat1785 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c310 := h 309 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c1700 := derived1700 a h
  have h17 : Entails.eval a c372 := h 371 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c277 := h 276 (by decide)
  have h20 : Entails.eval a c89 := h 88 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  have h22 : Entails.eval a c293 := h 292 (by decide)
  have h23 : Entails.eval a c1780 := derived1780 a h
  have h24 : Entails.eval a c1782 := derived1782 a h
  have h25 : Entails.eval a c207 := h 206 (by decide)
  have h26 : Entails.eval a c205 := h 204 (by decide)
  have h27 : Entails.eval a c444 := derived444 a h
  have h28 : Entails.eval a c1781 := derived1781 a h
  have h29 : Entails.eval a c1783 := derived1783 a h
  have h30 : Entails.eval a c157 := h 156 (by decide)
  have h31 : Entails.eval a c160 := h 159 (by decide)
  have h32 : Entails.eval a c12 := h 11 (by decide)
  have h33 : Entails.eval a c1784 := derived1784 a h
  have h34 : Entails.eval a c146 := h 145 (by decide)
  have h35 : Entails.eval a c126 := h 125 (by decide)
  have h36 : Entails.eval a c176 := h 175 (by decide)
  have h37 : Entails.eval a c1068 := derived1068 a h
  have h38 : Entails.eval a c1223 := derived1223 a h
  have h39 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1786 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, false), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨43, by decide⟩, false), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c28, some c198, some c216, some c231, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1786 : lratChecker f1786 p1786 = .success := by decide +kernel
theorem unsat1786 : Unsatisfiable (PosFin 57) f1786 := by
  apply lratCheckerSound f1786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1786
  · intro a ha; simp [p1786] at ha; subst a; trivial
  · exact checked1786
theorem derived1786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1786 := by
  apply localUnsat_implies_entails f1786 [c17, c28, c198, c216, c231] c1786 unsat1786 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1787 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c139, some c174, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1787 : lratChecker f1787 p1787 = .success := by decide +kernel
theorem unsat1787 : Unsatisfiable (PosFin 57) f1787 := by
  apply lratCheckerSound f1787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1787
  · intro a ha; simp [p1787] at ha; subst a; trivial
  · exact checked1787
theorem derived1787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1787 := by
  apply localUnsat_implies_entails f1787 [c137, c139, c174] c1787 unsat1787 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1788 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨9, by decide⟩, true), (⟨52, by decide⟩, true), (⟨37, by decide⟩, false), (⟨51, by decide⟩, true), (⟨4, by decide⟩, false), (⟨56, by decide⟩, false), (⟨35, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1700, some c841, some c1779, some c98, some c12, some c142, some c152, some c174, some c1244, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1788 : lratChecker f1788 p1788 = .success := by decide +kernel
theorem unsat1788 : Unsatisfiable (PosFin 57) f1788 := by
  apply lratCheckerSound f1788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1788
  · intro a ha; simp [p1788] at ha; subst a; trivial
  · exact checked1788
theorem derived1788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1788 := by
  apply localUnsat_implies_entails f1788 [c1671, c1700, c841, c1779, c98, c12, c142, c152, c174, c1244] c1788 unsat1788 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1700 := derived1700 a h
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c1244 := derived1244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1789 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨48, by decide⟩, true), (⟨35, by decide⟩, false), (⟨32, by decide⟩, false), (⟨45, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c310, some c34, some c1779, some c98, some c72, some c841, some c89, some c333, some c336, some c348, some c1700, some c200, some c193, some c244, some c217, some c29, some c242, some c1781, some c1788, some c167, some c114, some c131, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1789 : lratChecker f1789 p1789 = .success := by decide +kernel
theorem unsat1789 : Unsatisfiable (PosFin 57) f1789 := by
  apply lratCheckerSound f1789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1789
  · intro a ha; simp [p1789] at ha; subst a; trivial
  · exact checked1789
theorem derived1789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1789 := by
  apply localUnsat_implies_entails f1789 [c1671, c310, c34, c1779, c98, c72, c841, c89, c333, c336, c348, c1700, c200, c193, c244, c217, c29, c242, c1781, c1788, c167, c114, c131] c1789 unsat1789 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c1700 := derived1700 a h
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c244 := h 243 (by decide)
  have h15 : Entails.eval a c217 := h 216 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  have h18 : Entails.eval a c1781 := derived1781 a h
  have h19 : Entails.eval a c1788 := derived1788 a h
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1790 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, true), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c336, some c219, some c244, some c197, some c254, some c255, some c218, some c1787, some c160, some c109, some c130, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1790 : lratChecker f1790 p1790 = .success := by decide +kernel
theorem unsat1790 : Unsatisfiable (PosFin 57) f1790 := by
  apply lratCheckerSound f1790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1790
  · intro a ha; simp [p1790] at ha; subst a; trivial
  · exact checked1790
theorem derived1790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1790 := by
  apply localUnsat_implies_entails f1790 [c333, c336, c219, c244, c197, c254, c255, c218, c1787, c160, c109, c130] c1790 unsat1790 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c244 := h 243 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c254 := h 253 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c1787 := derived1787 a h
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1791 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, false), (⟨56, by decide⟩, false), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨45, by decide⟩, true), (⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c841, some c89, some c333, some c348, some c60, some c1700, some c1779, some c447, some c220, some c1781, some c1787, some c160, some c12, some c130, some c1788, some c1223, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1791 : lratChecker f1791 p1791 = .success := by decide +kernel
theorem unsat1791 : Unsatisfiable (PosFin 57) f1791 := by
  apply lratCheckerSound f1791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1791
  · intro a ha; simp [p1791] at ha; subst a; trivial
  · exact checked1791
theorem derived1791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1791 := by
  apply localUnsat_implies_entails f1791 [c1671, c841, c89, c333, c348, c60, c1700, c1779, c447, c220, c1781, c1787, c160, c12, c130, c1788, c1223] c1791 unsat1791 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c841 := derived841 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c1700 := derived1700 a h
  have h7 : Entails.eval a c1779 := derived1779 a h
  have h8 : Entails.eval a c447 := derived447 a h
  have h9 : Entails.eval a c220 := h 219 (by decide)
  have h10 : Entails.eval a c1781 := derived1781 a h
  have h11 : Entails.eval a c1787 := derived1787 a h
  have h12 : Entails.eval a c160 := h 159 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c1788 := derived1788 a h
  have h16 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1792 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨43, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1785, some c283, some c372, some c1779, some c98, some c1671, some c47, some c35, some c288, some c310, some c306, some c323, some c72, some c34, some c841, some c1700, some c317, some c348, some c89, some c60, some c333, some c1786, some c1789, some c1790, some c1791, some c231, some c198, some c18, some c255, some c223, some c1781, some c157, some c137, some c174, some c111, some c186, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1792 : lratChecker f1792 p1792 = .success := by decide +kernel
theorem unsat1792 : Unsatisfiable (PosFin 57) f1792 := by
  apply lratCheckerSound f1792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1792
  · intro a ha; simp [p1792] at ha; subst a; trivial
  · exact checked1792
theorem derived1792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1792 := by
  apply localUnsat_implies_entails f1792 [c1785, c283, c372, c1779, c98, c1671, c47, c35, c288, c310, c306, c323, c72, c34, c841, c1700, c317, c348, c89, c60, c333, c1786, c1789, c1790, c1791, c231, c198, c18, c255, c223, c1781, c157, c137, c174, c111, c186] c1792 unsat1792 (by rfl) a
  have h0 : Entails.eval a c1785 := derived1785 a h
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c310 := h 309 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c1700 := derived1700 a h
  have h16 : Entails.eval a c317 := h 316 (by decide)
  have h17 : Entails.eval a c348 := h 347 (by decide)
  have h18 : Entails.eval a c89 := h 88 (by decide)
  have h19 : Entails.eval a c60 := h 59 (by decide)
  have h20 : Entails.eval a c333 := h 332 (by decide)
  have h21 : Entails.eval a c1786 := derived1786 a h
  have h22 : Entails.eval a c1789 := derived1789 a h
  have h23 : Entails.eval a c1790 := derived1790 a h
  have h24 : Entails.eval a c1791 := derived1791 a h
  have h25 : Entails.eval a c231 := h 230 (by decide)
  have h26 : Entails.eval a c198 := h 197 (by decide)
  have h27 : Entails.eval a c18 := h 17 (by decide)
  have h28 : Entails.eval a c255 := h 254 (by decide)
  have h29 : Entails.eval a c223 := h 222 (by decide)
  have h30 : Entails.eval a c1781 := derived1781 a h
  have h31 : Entails.eval a c157 := h 156 (by decide)
  have h32 : Entails.eval a c137 := h 136 (by decide)
  have h33 : Entails.eval a c174 := h 173 (by decide)
  have h34 : Entails.eval a c111 := h 110 (by decide)
  have h35 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1793 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨43, by decide⟩, false), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1251, some c1671, some c57, some c60, some c334, some c66, some c368, some c81, some c288, some c320, some c40, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1793 : lratChecker f1793 p1793 = .success := by decide +kernel
theorem unsat1793 : Unsatisfiable (PosFin 57) f1793 := by
  apply lratCheckerSound f1793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1793
  · intro a ha; simp [p1793] at ha; subst a; trivial
  · exact checked1793
theorem derived1793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1793 := by
  apply localUnsat_implies_entails f1793 [c1779, c98, c1251, c1671, c57, c60, c334, c66, c368, c81, c288, c320, c40] c1793 unsat1793 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1794 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨21, by decide⟩, true), (⟨35, by decide⟩, true), (⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1251, some c1671, some c193, some c345, some c262, some c306, some c40, some c49, some c207, some c328, some c309, some c72, some c841, some c571, some c89, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1794 : lratChecker f1794 p1794 = .success := by decide +kernel
theorem unsat1794 : Unsatisfiable (PosFin 57) f1794 := by
  apply lratCheckerSound f1794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1794
  · intro a ha; simp [p1794] at ha; subst a; trivial
  · exact checked1794
theorem derived1794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1794 := by
  apply localUnsat_implies_entails f1794 [c1779, c98, c1251, c1671, c193, c345, c262, c306, c40, c49, c207, c328, c309, c72, c841, c571, c89] c1794 unsat1794 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c571 := derived571 a h
  have h16 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1795 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1785, some c1779, some c98, some c1671, some c283, some c1792, some c103, some c1251, some c1793, some c323, some c191, some c26, some c1794, some c305, some c262, some c345, some c347, some c219, some c40, some c288, some c310, some c72, some c841, some c571, some c89, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1795 : lratChecker f1795 p1795 = .success := by decide +kernel
theorem unsat1795 : Unsatisfiable (PosFin 57) f1795 := by
  apply lratCheckerSound f1795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1795
  · intro a ha; simp [p1795] at ha; subst a; trivial
  · exact checked1795
theorem derived1795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1795 := by
  apply localUnsat_implies_entails f1795 [c1785, c1779, c98, c1671, c283, c1792, c103, c1251, c1793, c323, c191, c26, c1794, c305, c262, c345, c347, c219, c40, c288, c310, c72, c841, c571, c89] c1795 unsat1795 (by rfl) a
  have h0 : Entails.eval a c1785 := derived1785 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c1792 := derived1792 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c1793 := derived1793 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c1794 := derived1794 a h
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c347 := h 346 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c40 := h 39 (by decide)
  have h19 : Entails.eval a c288 := h 287 (by decide)
  have h20 : Entails.eval a c310 := h 309 (by decide)
  have h21 : Entails.eval a c72 := h 71 (by decide)
  have h22 : Entails.eval a c841 := derived841 a h
  have h23 : Entails.eval a c571 := derived571 a h
  have h24 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1796 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨54, by decide⟩, false), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨42, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨41, by decide⟩, true), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c220, some c216, some c243, some c197, some c290, some c149, some c1, some c119, some c160, some c112, some c138, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1796 : lratChecker f1796 p1796 = .success := by decide +kernel
theorem unsat1796 : Unsatisfiable (PosFin 57) f1796 := by
  apply lratCheckerSound f1796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1796
  · intro a ha; simp [p1796] at ha; subst a; trivial
  · exact checked1796
theorem derived1796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1796 := by
  apply localUnsat_implies_entails f1796 [c220, c216, c243, c197, c290, c149, c1, c119, c160, c112, c138] c1796 unsat1796 (by rfl) a
  have h0 : Entails.eval a c220 := h 219 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1797 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨52, by decide⟩, true), (⟨35, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, false), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c288, some c40, some c336, some c93, some c28, some c17, some c320, some c328, some c367, some c1796, some c236, some c260, some c205, some c214, some c243, some c197, some c290, some c149, some c355, some c2, some c1, some c285, some c166, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1797 : lratChecker f1797 p1797 = .success := by decide +kernel
theorem unsat1797 : Unsatisfiable (PosFin 57) f1797 := by
  apply lratCheckerSound f1797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1797
  · intro a ha; simp [p1797] at ha; subst a; trivial
  · exact checked1797
theorem derived1797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1797 := by
  apply localUnsat_implies_entails f1797 [c1779, c98, c288, c40, c336, c93, c28, c17, c320, c328, c367, c1796, c236, c260, c205, c214, c243, c197, c290, c149, c355, c2, c1, c285, c166] c1797 unsat1797 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c336 := h 335 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c1796 := derived1796 a h
  have h12 : Entails.eval a c236 := h 235 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c214 := h 213 (by decide)
  have h16 : Entails.eval a c243 := h 242 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c149 := h 148 (by decide)
  have h20 : Entails.eval a c355 := h 354 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c1 := h 0 (by decide)
  have h23 : Entails.eval a c285 := h 284 (by decide)
  have h24 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1798 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, true), (⟨45, by decide⟩, true), (⟨42, by decide⟩, true), (⟨55, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c157, some c160, some c1482, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1798 : lratChecker f1798 p1798 = .success := by decide +kernel
theorem unsat1798 : Unsatisfiable (PosFin 57) f1798 := by
  apply lratCheckerSound f1798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1798
  · intro a ha; simp [p1798] at ha; subst a; trivial
  · exact checked1798
theorem derived1798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1798 := by
  apply localUnsat_implies_entails f1798 [c1779, c157, c160, c1482] c1798 unsat1798 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c1482 := derived1482 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1799 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c1779, some c98, some c288, some c40, some c336, some c93, some c28, some c333, some c320, some c328, some c367, some c1797, some c1798, some c140, some c177, some c13, some c12, some c184, some c138, some c178, some c216, some c246, some c236, some c111, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1799 : lratChecker f1799 p1799 = .success := by decide +kernel
theorem unsat1799 : Unsatisfiable (PosFin 57) f1799 := by
  apply lratCheckerSound f1799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1799
  · intro a ha; simp [p1799] at ha; subst a; trivial
  · exact checked1799
theorem derived1799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1799 := by
  apply localUnsat_implies_entails f1799 [c376, c1779, c98, c288, c40, c336, c93, c28, c333, c320, c328, c367, c1797, c1798, c140, c177, c13, c12, c184, c138, c178, c216, c246, c236, c111] c1799 unsat1799 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c1797 := derived1797 a h
  have h13 : Entails.eval a c1798 := derived1798 a h
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c138 := h 137 (by decide)
  have h20 : Entails.eval a c178 := h 177 (by decide)
  have h21 : Entails.eval a c216 := h 215 (by decide)
  have h22 : Entails.eval a c246 := h 245 (by decide)
  have h23 : Entails.eval a c236 := h 235 (by decide)
  have h24 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1800 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨41, by decide⟩, true), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c243, some c197, some c290, some c149, some c119, some c112, some c109, some c138, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1800 : lratChecker f1800 p1800 = .success := by decide +kernel
theorem unsat1800 : Unsatisfiable (PosFin 57) f1800 := by
  apply lratCheckerSound f1800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1800
  · intro a ha; simp [p1800] at ha; subst a; trivial
  · exact checked1800
theorem derived1800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1800 := by
  apply localUnsat_implies_entails f1800 [c243, c197, c290, c149, c119, c112, c109, c138] c1800 unsat1800 (by rfl) a
  have h0 : Entails.eval a c243 := h 242 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1801 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨22, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨42, by decide⟩, true), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨27, by decide⟩, false), (⟨40, by decide⟩, false), (⟨41, by decide⟩, true), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c299, some c1779, some c189, some c197, some c258, some c241, some c450, some c157, some c2, some c136, some c180, some c111, some c127, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1801 : lratChecker f1801 p1801 = .success := by decide +kernel
theorem unsat1801 : Unsatisfiable (PosFin 57) f1801 := by
  apply lratCheckerSound f1801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1801
  · intro a ha; simp [p1801] at ha; subst a; trivial
  · exact checked1801
theorem derived1801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1801 := by
  apply localUnsat_implies_entails f1801 [c293, c299, c1779, c189, c197, c258, c241, c450, c157, c2, c136, c180, c111, c127] c1801 unsat1801 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c450 := derived450 a h
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1802 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨36, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨42, by decide⟩, true), (⟨34, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c107, some c138, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1802 : lratChecker f1802 p1802 = .success := by decide +kernel
theorem unsat1802 : Unsatisfiable (PosFin 57) f1802 := by
  apply lratCheckerSound f1802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1802
  · intro a ha; simp [p1802] at ha; subst a; trivial
  · exact checked1802
theorem derived1802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1802 := by
  apply localUnsat_implies_entails f1802 [c157, c107, c138] c1802 unsat1802 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1803 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨50, by decide⟩, false), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨27, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨31, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c1779, some c98, some c288, some c40, some c336, some c93, some c293, some c320, some c299, some c328, some c367, some c17, some c28, some c1799, some c234, some c220, some c216, some c1800, some c1801, some c1802, some c2, some c119, some c180, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1803 : lratChecker f1803 p1803 = .success := by decide +kernel
theorem unsat1803 : Unsatisfiable (PosFin 57) f1803 := by
  apply lratCheckerSound f1803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1803
  · intro a ha; simp [p1803] at ha; subst a; trivial
  · exact checked1803
theorem derived1803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1803 := by
  apply localUnsat_implies_entails f1803 [c376, c1779, c98, c288, c40, c336, c93, c293, c320, c299, c328, c367, c17, c28, c1799, c234, c220, c216, c1800, c1801, c1802, c2, c119, c180] c1803 unsat1803 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c1799 := derived1799 a h
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c216 := h 215 (by decide)
  have h18 : Entails.eval a c1800 := derived1800 a h
  have h19 : Entails.eval a c1801 := derived1801 a h
  have h20 : Entails.eval a c1802 := derived1802 a h
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c119 := h 118 (by decide)
  have h23 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1804 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1795, some c1785, some c1779, some c98, some c1671, some c67, some c79, some c288, some c40, some c47, some c328, some c1707, some c299, some c312, some c57, some c89, some c293, some c1803, some c207, some c200, some c236, some c258, some c220, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1804 : lratChecker f1804 p1804 = .success := by decide +kernel
theorem unsat1804 : Unsatisfiable (PosFin 57) f1804 := by
  apply lratCheckerSound f1804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1804
  · intro a ha; simp [p1804] at ha; subst a; trivial
  · exact checked1804
theorem derived1804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1804 := by
  apply localUnsat_implies_entails f1804 [c1795, c1785, c1779, c98, c1671, c67, c79, c288, c40, c47, c328, c1707, c299, c312, c57, c89, c293, c1803, c207, c200, c236, c258, c220] c1804 unsat1804 (by rfl) a
  have h0 : Entails.eval a c1795 := derived1795 a h
  have h1 : Entails.eval a c1785 := derived1785 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c1707 := derived1707 a h
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c293 := h 292 (by decide)
  have h17 : Entails.eval a c1803 := derived1803 a h
  have h18 : Entails.eval a c207 := h 206 (by decide)
  have h19 : Entails.eval a c200 := h 199 (by decide)
  have h20 : Entails.eval a c236 := h 235 (by decide)
  have h21 : Entails.eval a c258 := h 257 (by decide)
  have h22 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1805 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1251, some c1671, some c57, some c60, some c334, some c66, some c318, some c81, some c288, some c320, some c40, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1805 : lratChecker f1805 p1805 = .success := by decide +kernel
theorem unsat1805 : Unsatisfiable (PosFin 57) f1805 := by
  apply lratCheckerSound f1805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1805
  · intro a ha; simp [p1805] at ha; subst a; trivial
  · exact checked1805
theorem derived1805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1805 := by
  apply localUnsat_implies_entails f1805 [c1779, c98, c1251, c1671, c57, c60, c334, c66, c318, c81, c288, c320, c40] c1805 unsat1805 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1251 := derived1251 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1806 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c328, some c40, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1806 : lratChecker f1806 p1806 = .success := by decide +kernel
theorem unsat1806 : Unsatisfiable (PosFin 57) f1806 := by
  apply lratCheckerSound f1806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1806
  · intro a ha; simp [p1806] at ha; subst a; trivial
  · exact checked1806
theorem derived1806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1806 := by
  apply localUnsat_implies_entails f1806 [c288, c328, c40] c1806 unsat1806 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1807 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1671, some c1785, some c1804, some c103, some c1251, some c1805, some c1806, some c72, some c841, some c89, some c569, some c34, some c310, some c309, some c49, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1807 : lratChecker f1807 p1807 = .success := by decide +kernel
theorem unsat1807 : Unsatisfiable (PosFin 57) f1807 := by
  apply lratCheckerSound f1807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1807
  · intro a ha; simp [p1807] at ha; subst a; trivial
  · exact checked1807
theorem derived1807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1807 := by
  apply localUnsat_implies_entails f1807 [c1779, c98, c1671, c1785, c1804, c103, c1251, c1805, c1806, c72, c841, c89, c569, c34, c310, c309, c49] c1807 unsat1807 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1785 := derived1785 a h
  have h4 : Entails.eval a c1804 := derived1804 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c1251 := derived1251 a h
  have h7 : Entails.eval a c1805 := derived1805 a h
  have h8 : Entails.eval a c1806 := derived1806 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c569 := derived569 a h
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1808 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c219, some c212, some c236, some c258, some c208, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p1808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1808 : lratChecker f1808 p1808 = .success := by decide +kernel
theorem unsat1808 : Unsatisfiable (PosFin 57) f1808 := by
  apply lratCheckerSound f1808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1808
  · intro a ha; simp [p1808] at ha; subst a; trivial
  · exact checked1808
theorem derived1808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1808 := by
  apply localUnsat_implies_entails f1808 [c219, c212, c236, c258, c208] c1808 unsat1808 (by rfl) a
  have h0 : Entails.eval a c219 := h 218 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1809 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨28, by decide⟩, false), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c1779, some c98, some c2, some c1, some c166, some c160, some c1534, some c439, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1809 : lratChecker f1809 p1809 = .success := by decide +kernel
theorem unsat1809 : Unsatisfiable (PosFin 57) f1809 := by
  apply lratCheckerSound f1809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1809
  · intro a ha; simp [p1809] at ha; subst a; trivial
  · exact checked1809
theorem derived1809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1809 := by
  apply localUnsat_implies_entails f1809 [c280, c1779, c98, c2, c1, c166, c160, c1534, c439] c1809 unsat1809 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c1534 := derived1534 a h
  have h8 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1810 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨43, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c107, some c158, some c184, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p1810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1810 : lratChecker f1810 p1810 = .success := by decide +kernel
theorem unsat1810 : Unsatisfiable (PosFin 57) f1810 := by
  apply lratCheckerSound f1810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1810
  · intro a ha; simp [p1810] at ha; subst a; trivial
  · exact checked1810
theorem derived1810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1810 := by
  apply localUnsat_implies_entails f1810 [c157, c107, c158, c184] c1810 unsat1810 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1811 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨9, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c1779, some c2, some c280, some c98, some c1809, some c166, some c153, some c160, some c192, some c1534, some c246, some c124, some c113, some c111, some c141, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1811 : lratChecker f1811 p1811 = .success := by decide +kernel
theorem unsat1811 : Unsatisfiable (PosFin 57) f1811 := by
  apply lratCheckerSound f1811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1811
  · intro a ha; simp [p1811] at ha; subst a; trivial
  · exact checked1811
theorem derived1811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1811 := by
  apply localUnsat_implies_entails f1811 [c1, c1779, c2, c280, c98, c1809, c166, c153, c160, c192, c1534, c246, c124, c113, c111, c141] c1811 unsat1811 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1809 := derived1809 a h
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c1534 := derived1534 a h
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1812 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨23, by decide⟩, true), (⟨9, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨26, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c208, some c243, some c1035, some c953, some c112, some c122, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1812 : lratChecker f1812 p1812 = .success := by decide +kernel
theorem unsat1812 : Unsatisfiable (PosFin 57) f1812 := by
  apply lratCheckerSound f1812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1812
  · intro a ha; simp [p1812] at ha; subst a; trivial
  · exact checked1812
theorem derived1812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1812 := by
  apply localUnsat_implies_entails f1812 [c204, c208, c243, c1035, c953, c112, c122] c1812 unsat1812 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c1035 := derived1035 a h
  have h4 : Entails.eval a c953 := derived953 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1813 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨48, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c39, some c328, some c40, some c1671, some c45, some c280, some c66, some c296, some c367, some c1807, some c59, some c91, some c323, some c352, some c339, some c333, some c376, some c1251, some c1808, some c17, some c28, some c1810, some c2, some c1, some c1811, some c234, some c1812, some c154, some c180, some c178, some c1534, some c183, some c143, some c246, some c111, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1813 : lratChecker f1813 p1813 = .success := by decide +kernel
theorem unsat1813 : Unsatisfiable (PosFin 57) f1813 := by
  apply lratCheckerSound f1813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1813
  · intro a ha; simp [p1813] at ha; subst a; trivial
  · exact checked1813
theorem derived1813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1813 := by
  apply localUnsat_implies_entails f1813 [c1779, c98, c39, c328, c40, c1671, c45, c280, c66, c296, c367, c1807, c59, c91, c323, c352, c339, c333, c376, c1251, c1808, c17, c28, c1810, c2, c1, c1811, c234, c1812, c154, c180, c178, c1534, c183, c143, c246, c111] c1813 unsat1813 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c1807 := derived1807 a h
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c323 := h 322 (by decide)
  have h15 : Entails.eval a c352 := h 351 (by decide)
  have h16 : Entails.eval a c339 := h 338 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c376 := h 375 (by decide)
  have h19 : Entails.eval a c1251 := derived1251 a h
  have h20 : Entails.eval a c1808 := derived1808 a h
  have h21 : Entails.eval a c17 := h 16 (by decide)
  have h22 : Entails.eval a c28 := h 27 (by decide)
  have h23 : Entails.eval a c1810 := derived1810 a h
  have h24 : Entails.eval a c2 := h 1 (by decide)
  have h25 : Entails.eval a c1 := h 0 (by decide)
  have h26 : Entails.eval a c1811 := derived1811 a h
  have h27 : Entails.eval a c234 := h 233 (by decide)
  have h28 : Entails.eval a c1812 := derived1812 a h
  have h29 : Entails.eval a c154 := h 153 (by decide)
  have h30 : Entails.eval a c180 := h 179 (by decide)
  have h31 : Entails.eval a c178 := h 177 (by decide)
  have h32 : Entails.eval a c1534 := derived1534 a h
  have h33 : Entails.eval a c183 := h 182 (by decide)
  have h34 : Entails.eval a c143 := h 142 (by decide)
  have h35 : Entails.eval a c246 := h 245 (by decide)
  have h36 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1814 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c45, some c39, some c1779, some c98, some c328, some c40, some c280, some c66, some c1813, some c103, some c1251, some c1170, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1814 : lratChecker f1814 p1814 = .success := by decide +kernel
theorem unsat1814 : Unsatisfiable (PosFin 57) f1814 := by
  apply lratCheckerSound f1814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1814
  · intro a ha; simp [p1814] at ha; subst a; trivial
  · exact checked1814
theorem derived1814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1814 := by
  apply localUnsat_implies_entails f1814 [c1671, c45, c39, c1779, c98, c328, c40, c280, c66, c1813, c103, c1251, c1170] c1814 unsat1814 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c1813 := derived1813 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1251 := derived1251 a h
  have h12 : Entails.eval a c1170 := derived1170 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1815 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨26, by decide⟩, false), (⟨39, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c72, some c296, some c40, some c336, some c347, some c841, some c79, some c47, some c372, some c323, some c277, some c293, some c308, some c49, some c1780, some c1782, some c444, some c208, some c231, some c210, some c223, some c1798, some c121, some c174, some c1213, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1815 : lratChecker f1815 p1815 = .success := by decide +kernel
theorem unsat1815 : Unsatisfiable (PosFin 57) f1815 := by
  apply lratCheckerSound f1815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1815
  · intro a ha; simp [p1815] at ha; subst a; trivial
  · exact checked1815
theorem derived1815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1815 := by
  apply localUnsat_implies_entails f1815 [c1779, c98, c72, c296, c40, c336, c347, c841, c79, c47, c372, c323, c277, c293, c308, c49, c1780, c1782, c444, c208, c231, c210, c223, c1798, c121, c174, c1213] c1815 unsat1815 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c347 := h 346 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c308 := h 307 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c1780 := derived1780 a h
  have h17 : Entails.eval a c1782 := derived1782 a h
  have h18 : Entails.eval a c444 := derived444 a h
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c231 := h 230 (by decide)
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c223 := h 222 (by decide)
  have h23 : Entails.eval a c1798 := derived1798 a h
  have h24 : Entails.eval a c121 := h 120 (by decide)
  have h25 : Entails.eval a c174 := h 173 (by decide)
  have h26 : Entails.eval a c1213 := derived1213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1816 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1807, some c1779, some c98, some c1671, some c39, some c45, some c1814, some c72, some c841, some c1700, some c89, some c1815, some c103, some c1251, some c1170, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1816 : lratChecker f1816 p1816 = .success := by decide +kernel
theorem unsat1816 : Unsatisfiable (PosFin 57) f1816 := by
  apply lratCheckerSound f1816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1816
  · intro a ha; simp [p1816] at ha; subst a; trivial
  · exact checked1816
theorem derived1816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1816 := by
  apply localUnsat_implies_entails f1816 [c1807, c1779, c98, c1671, c39, c45, c1814, c72, c841, c1700, c89, c1815, c103, c1251, c1170] c1816 unsat1816 (by rfl) a
  have h0 : Entails.eval a c1807 := derived1807 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c1814 := derived1814 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c1700 := derived1700 a h
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c1815 := derived1815 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c1251 := derived1251 a h
  have h14 : Entails.eval a c1170 := derived1170 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1817 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c207, some c258, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1817 : lratChecker f1817 p1817 = .success := by decide +kernel
theorem unsat1817 : Unsatisfiable (PosFin 57) f1817 := by
  apply lratCheckerSound f1817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1817
  · intro a ha; simp [p1817] at ha; subst a; trivial
  · exact checked1817
theorem derived1817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1817 := by
  apply localUnsat_implies_entails f1817 [c200, c207, c258] c1817 unsat1817 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1818 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨51, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨30, by decide⟩, true), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c166, some c153, some c160, some c1534, some c246, some c140, some c113, some c111, some c184, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1818 : lratChecker f1818 p1818 = .success := by decide +kernel
theorem unsat1818 : Unsatisfiable (PosFin 57) f1818 := by
  apply lratCheckerSound f1818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1818
  · intro a ha; simp [p1818] at ha; subst a; trivial
  · exact checked1818
theorem derived1818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1818 := by
  apply localUnsat_implies_entails f1818 [c320, c166, c153, c160, c1534, c246, c140, c113, c111, c184] c1818 unsat1818 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1534 := derived1534 a h
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1819 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨31, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c197, some c109, some c119, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true))]
def p1819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1819 : lratChecker f1819 p1819 = .success := by decide +kernel
theorem unsat1819 : Unsatisfiable (PosFin 57) f1819 := by
  apply lratCheckerSound f1819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1819
  · intro a ha; simp [p1819] at ha; subst a; trivial
  · exact checked1819
theorem derived1819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1819 := by
  apply localUnsat_implies_entails f1819 [c197, c109, c119] c1819 unsat1819 (by rfl) a
  have h0 : Entails.eval a c197 := h 196 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1820 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1816, some c1807, some c1779, some c98, some c1671, some c367, some c288, some c1806, some c40, some c57, some c1805, some c1707, some c320, some c103, some c194, some c66, some c47, some c18, some c29, some c336, some c283, some c312, some c1810, some c91, some c270, some c2, some c1, some c376, some c293, some c333, some c1817, some c1818, some c234, some c216, some c324, some c355, some c152, some c138, some c1819, some c241, some c243, some c210, some c178, some c329, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]]
theorem checked1820 : lratChecker f1820 p1820 = .success := by decide +kernel
theorem unsat1820 : Unsatisfiable (PosFin 57) f1820 := by
  apply lratCheckerSound f1820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1820
  · intro a ha; simp [p1820] at ha; subst a; trivial
  · exact checked1820
theorem derived1820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1820 := by
  apply localUnsat_implies_entails f1820 [c1816, c1807, c1779, c98, c1671, c367, c288, c1806, c40, c57, c1805, c1707, c320, c103, c194, c66, c47, c18, c29, c336, c283, c312, c1810, c91, c270, c2, c1, c376, c293, c333, c1817, c1818, c234, c216, c324, c355, c152, c138, c1819, c241, c243, c210, c178, c329] c1820 unsat1820 (by rfl) a
  have h0 : Entails.eval a c1816 := derived1816 a h
  have h1 : Entails.eval a c1807 := derived1807 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c1806 := derived1806 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c1805 := derived1805 a h
  have h11 : Entails.eval a c1707 := derived1707 a h
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c336 := h 335 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c312 := h 311 (by decide)
  have h22 : Entails.eval a c1810 := derived1810 a h
  have h23 : Entails.eval a c91 := h 90 (by decide)
  have h24 : Entails.eval a c270 := h 269 (by decide)
  have h25 : Entails.eval a c2 := h 1 (by decide)
  have h26 : Entails.eval a c1 := h 0 (by decide)
  have h27 : Entails.eval a c376 := h 375 (by decide)
  have h28 : Entails.eval a c293 := h 292 (by decide)
  have h29 : Entails.eval a c333 := h 332 (by decide)
  have h30 : Entails.eval a c1817 := derived1817 a h
  have h31 : Entails.eval a c1818 := derived1818 a h
  have h32 : Entails.eval a c234 := h 233 (by decide)
  have h33 : Entails.eval a c216 := h 215 (by decide)
  have h34 : Entails.eval a c324 := h 323 (by decide)
  have h35 : Entails.eval a c355 := h 354 (by decide)
  have h36 : Entails.eval a c152 := h 151 (by decide)
  have h37 : Entails.eval a c138 := h 137 (by decide)
  have h38 : Entails.eval a c1819 := derived1819 a h
  have h39 : Entails.eval a c241 := h 240 (by decide)
  have h40 : Entails.eval a c243 := h 242 (by decide)
  have h41 : Entails.eval a c210 := h 209 (by decide)
  have h42 : Entails.eval a c178 := h 177 (by decide)
  have h43 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1821 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨9, by decide⟩, true), (⟨55, by decide⟩, true), (⟨6, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1244, some c1226, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1821 : lratChecker f1821 p1821 = .success := by decide +kernel
theorem unsat1821 : Unsatisfiable (PosFin 57) f1821 := by
  apply lratCheckerSound f1821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1821
  · intro a ha; simp [p1821] at ha; subst a; trivial
  · exact checked1821
theorem derived1821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1821 := by
  apply localUnsat_implies_entails f1821 [c1244, c1226] c1821 unsat1821 (by rfl) a
  have h0 : Entails.eval a c1244 := derived1244 a h
  have h1 : Entails.eval a c1226 := derived1226 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1822 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨48, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c72, some c1700, some c841, some c1138, some c174, some c1821, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1822 : lratChecker f1822 p1822 = .success := by decide +kernel
theorem unsat1822 : Unsatisfiable (PosFin 57) f1822 := by
  apply lratCheckerSound f1822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1822
  · intro a ha; simp [p1822] at ha; subst a; trivial
  · exact checked1822
theorem derived1822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1822 := by
  apply localUnsat_implies_entails f1822 [c1671, c1779, c98, c72, c1700, c841, c1138, c174, c1821] c1822 unsat1822 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c1700 := derived1700 a h
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c1138 := derived1138 a h
  have h7 : Entails.eval a c174 := h 173 (by decide)
  have h8 : Entails.eval a c1821 := derived1821 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1823 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨42, by decide⟩, true), (⟨45, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨48, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c72, some c841, some c89, some c333, some c1822, some c1480, some c137, some c160, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1823 : lratChecker f1823 p1823 = .success := by decide +kernel
theorem unsat1823 : Unsatisfiable (PosFin 57) f1823 := by
  apply lratCheckerSound f1823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1823
  · intro a ha; simp [p1823] at ha; subst a; trivial
  · exact checked1823
theorem derived1823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1823 := by
  apply localUnsat_implies_entails f1823 [c1671, c1779, c98, c72, c841, c89, c333, c1822, c1480, c137, c160] c1823 unsat1823 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c1822 := derived1822 a h
  have h8 : Entails.eval a c1480 := derived1480 a h
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1824 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨30, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c137, some c1787, some c1138, some c174, some c194, some c185, some c18, some c29, some c107, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1824 : lratChecker f1824 p1824 = .success := by decide +kernel
theorem unsat1824 : Unsatisfiable (PosFin 57) f1824 := by
  apply lratCheckerSound f1824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1824
  · intro a ha; simp [p1824] at ha; subst a; trivial
  · exact checked1824
theorem derived1824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1824 := by
  apply localUnsat_implies_entails f1824 [c1779, c137, c1787, c1138, c174, c194, c185, c18, c29, c107] c1824 unsat1824 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c1787 := derived1787 a h
  have h3 : Entails.eval a c1138 := derived1138 a h
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1825 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, false), (⟨21, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨50, by decide⟩, false), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c447, some c1483, some c1223, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1825 : lratChecker f1825 p1825 = .success := by decide +kernel
theorem unsat1825 : Unsatisfiable (PosFin 57) f1825 := by
  apply lratCheckerSound f1825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1825
  · intro a ha; simp [p1825] at ha; subst a; trivial
  · exact checked1825
theorem derived1825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1825 := by
  apply localUnsat_implies_entails f1825 [c447, c1483, c1223] c1825 unsat1825 (by rfl) a
  have h0 : Entails.eval a c447 := derived447 a h
  have h1 : Entails.eval a c1483 := derived1483 a h
  have h2 : Entails.eval a c1223 := derived1223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1826 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c1820, some c72, some c841, some c89, some c1700, some c1816, some c1807, some c57, some c1805, some c336, some c103, some c40, some c79, some c59, some c307, some c372, some c283, some c317, some c333, some c348, some c1786, some c1823, some c1824, some c160, some c1798, some c12, some c1825, some c231, some c223, some c198, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1826 : lratChecker f1826 p1826 = .success := by decide +kernel
theorem unsat1826 : Unsatisfiable (PosFin 57) f1826 := by
  apply lratCheckerSound f1826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1826
  · intro a ha; simp [p1826] at ha; subst a; trivial
  · exact checked1826
theorem derived1826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1826 := by
  apply localUnsat_implies_entails f1826 [c1671, c1779, c98, c1820, c72, c841, c89, c1700, c1816, c1807, c57, c1805, c336, c103, c40, c79, c59, c307, c372, c283, c317, c333, c348, c1786, c1823, c1824, c160, c1798, c12, c1825, c231, c223, c198] c1826 unsat1826 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1820 := derived1820 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c1700 := derived1700 a h
  have h8 : Entails.eval a c1816 := derived1816 a h
  have h9 : Entails.eval a c1807 := derived1807 a h
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c1805 := derived1805 a h
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c79 := h 78 (by decide)
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  have h18 : Entails.eval a c372 := h 371 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c333 := h 332 (by decide)
  have h22 : Entails.eval a c348 := h 347 (by decide)
  have h23 : Entails.eval a c1786 := derived1786 a h
  have h24 : Entails.eval a c1823 := derived1823 a h
  have h25 : Entails.eval a c1824 := derived1824 a h
  have h26 : Entails.eval a c160 := h 159 (by decide)
  have h27 : Entails.eval a c1798 := derived1798 a h
  have h28 : Entails.eval a c12 := h 11 (by decide)
  have h29 : Entails.eval a c1825 := derived1825 a h
  have h30 : Entails.eval a c231 := h 230 (by decide)
  have h31 : Entails.eval a c223 := h 222 (by decide)
  have h32 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1827 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨48, by decide⟩, true), (⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c283, some c323, some c35, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1827 : lratChecker f1827 p1827 = .success := by decide +kernel
theorem unsat1827 : Unsatisfiable (PosFin 57) f1827 := by
  apply lratCheckerSound f1827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1827
  · intro a ha; simp [p1827] at ha; subst a; trivial
  · exact checked1827
theorem derived1827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1827 := by
  apply localUnsat_implies_entails f1827 [c79, c283, c323, c35] c1827 unsat1827 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1828 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1671, some c1816, some c1820, some c72, some c841, some c89, some c1826, some c1827, some c103, some c1251, some c569, some c34, some c296, some c294, some c49, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1828 : lratChecker f1828 p1828 = .success := by decide +kernel
theorem unsat1828 : Unsatisfiable (PosFin 57) f1828 := by
  apply lratCheckerSound f1828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1828
  · intro a ha; simp [p1828] at ha; subst a; trivial
  · exact checked1828
theorem derived1828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1828 := by
  apply localUnsat_implies_entails f1828 [c1779, c98, c1671, c1816, c1820, c72, c841, c89, c1826, c1827, c103, c1251, c569, c34, c296, c294, c49] c1828 unsat1828 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1816 := derived1816 a h
  have h4 : Entails.eval a c1820 := derived1820 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c1826 := derived1826 a h
  have h9 : Entails.eval a c1827 := derived1827 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c1251 := derived1251 a h
  have h12 : Entails.eval a c569 := derived569 a h
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c294 := h 293 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1829 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1828, some c1779, some c98, some c1671, some c57, some c39, some c1754, some c288, some c76, some c40, some c320, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1829 : lratChecker f1829 p1829 = .success := by decide +kernel
theorem unsat1829 : Unsatisfiable (PosFin 57) f1829 := by
  apply lratCheckerSound f1829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1829
  · intro a ha; simp [p1829] at ha; subst a; trivial
  · exact checked1829
theorem derived1829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1829 := by
  apply localUnsat_implies_entails f1829 [c1828, c1779, c98, c1671, c57, c39, c1754, c288, c76, c40, c320] c1829 unsat1829 (by rfl) a
  have h0 : Entails.eval a c1828 := derived1828 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c1754 := derived1754 a h
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1830 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1828, some c1779, some c98, some c1671, some c1829, some c1806, some c328, some c45, some c40, some c63, some c280, some c326, some c76, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1830 : lratChecker f1830 p1830 = .success := by decide +kernel
theorem unsat1830 : Unsatisfiable (PosFin 57) f1830 := by
  apply lratCheckerSound f1830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1830
  · intro a ha; simp [p1830] at ha; subst a; trivial
  · exact checked1830
theorem derived1830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1830 := by
  apply localUnsat_implies_entails f1830 [c1828, c1779, c98, c1671, c1829, c1806, c328, c45, c40, c63, c280, c326, c76] c1830 unsat1830 (by rfl) a
  have h0 : Entails.eval a c1828 := derived1828 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c1829 := derived1829 a h
  have h5 : Entails.eval a c1806 := derived1806 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1831 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1779, some c98, some c1830, some c72, some c841, some c89, some c1828, some c83, some c57, some c39, some c336, some c286, some c40, some c44, some c296, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1831 : lratChecker f1831 p1831 = .success := by decide +kernel
theorem unsat1831 : Unsatisfiable (PosFin 57) f1831 := by
  apply lratCheckerSound f1831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1831
  · intro a ha; simp [p1831] at ha; subst a; trivial
  · exact checked1831
theorem derived1831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1831 := by
  apply localUnsat_implies_entails f1831 [c1671, c1779, c98, c1830, c72, c841, c89, c1828, c83, c57, c39, c336, c286, c40, c44, c296] c1831 unsat1831 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1830 := derived1830 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c1828 := derived1828 a h
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1832 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1671, some c1828, some c1830, some c72, some c83, some c841, some c89, some c1831, some c326, some c63, some c56, some c336, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1832 : lratChecker f1832 p1832 = .success := by decide +kernel
theorem unsat1832 : Unsatisfiable (PosFin 57) f1832 := by
  apply lratCheckerSound f1832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1832
  · intro a ha; simp [p1832] at ha; subst a; trivial
  · exact checked1832
theorem derived1832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1832 := by
  apply localUnsat_implies_entails f1832 [c1779, c98, c1671, c1828, c1830, c72, c83, c841, c89, c1831, c326, c63, c56, c336] c1832 unsat1832 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1828 := derived1828 a h
  have h4 : Entails.eval a c1830 := derived1830 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c1831 := derived1831 a h
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1833 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨25, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c769, some c780, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1833 : lratChecker f1833 p1833 = .success := by decide +kernel
theorem unsat1833 : Unsatisfiable (PosFin 57) f1833 := by
  apply lratCheckerSound f1833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1833
  · intro a ha; simp [p1833] at ha; subst a; trivial
  · exact checked1833
theorem derived1833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1833 := by
  apply localUnsat_implies_entails f1833 [c1779, c769, c780] c1833 unsat1833 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c769 := derived769 a h
  have h2 : Entails.eval a c780 := derived780 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1834 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨45, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c329, some c149, some c2, some c133, some c166, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1834 : lratChecker f1834 p1834 = .success := by decide +kernel
theorem unsat1834 : Unsatisfiable (PosFin 57) f1834 := by
  apply lratCheckerSound f1834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1834
  · intro a ha; simp [p1834] at ha; subst a; trivial
  · exact checked1834
theorem derived1834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1834 := by
  apply localUnsat_implies_entails f1834 [c1779, c329, c149, c2, c133, c166] c1834 unsat1834 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1835 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1832, some c97, some c1414, some c1671, some c1754, some c288, some c76, some c69, some c40, some c51, some c370, some c1005, some c320, some c305, some c34, some c1834, some c769, some c1833, some c309, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1835 : lratChecker f1835 p1835 = .success := by decide +kernel
theorem unsat1835 : Unsatisfiable (PosFin 57) f1835 := by
  apply lratCheckerSound f1835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1835
  · intro a ha; simp [p1835] at ha; subst a; trivial
  · exact checked1835
theorem derived1835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1835 := by
  apply localUnsat_implies_entails f1835 [c1779, c98, c1832, c97, c1414, c1671, c1754, c288, c76, c69, c40, c51, c370, c1005, c320, c305, c34, c1834, c769, c1833, c309] c1835 unsat1835 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1832 := derived1832 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c1414 := derived1414 a h
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c1754 := derived1754 a h
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c1005 := derived1005 a h
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c1834 := derived1834 a h
  have h18 : Entails.eval a c769 := derived769 a h
  have h19 : Entails.eval a c1833 := derived1833 a h
  have h20 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1836 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c1779, some c98, some c1671, some c404, some c413, some c49, some c205, some c29, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1836 : lratChecker f1836 p1836 = .success := by decide +kernel
theorem unsat1836 : Unsatisfiable (PosFin 57) f1836 := by
  apply lratCheckerSound f1836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1836
  · intro a ha; simp [p1836] at ha; subst a; trivial
  · exact checked1836
theorem derived1836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1836 := by
  apply localUnsat_implies_entails f1836 [c97, c1779, c98, c1671, c404, c413, c49, c205, c29] c1836 unsat1836 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c404 := derived404 a h
  have h5 : Entails.eval a c413 := derived413 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1837 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1835, some c195, some c236, some c1832, some c19, some c1779, some c98, some c97, some c1414, some c1671, some c320, some c350, some c66, some c76, some c272, some c336, some c372, some c234, some c1758, some c95, some c1760, some c218, some c1836, some c310, some c306, some c287, some c197, some c243, some c257, some c154, some c1810, some c2, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1837 : lratChecker f1837 p1837 = .success := by decide +kernel
theorem unsat1837 : Unsatisfiable (PosFin 57) f1837 := by
  apply lratCheckerSound f1837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1837
  · intro a ha; simp [p1837] at ha; subst a; trivial
  · exact checked1837
theorem derived1837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1837 := by
  apply localUnsat_implies_entails f1837 [c1835, c195, c236, c1832, c19, c1779, c98, c97, c1414, c1671, c320, c350, c66, c76, c272, c336, c372, c234, c1758, c95, c1760, c218, c1836, c310, c306, c287, c197, c243, c257, c154, c1810, c2] c1837 unsat1837 (by rfl) a
  have h0 : Entails.eval a c1835 := derived1835 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c1832 := derived1832 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c1779 := derived1779 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c350 := h 349 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c234 := h 233 (by decide)
  have h18 : Entails.eval a c1758 := derived1758 a h
  have h19 : Entails.eval a c95 := h 94 (by decide)
  have h20 : Entails.eval a c1760 := derived1760 a h
  have h21 : Entails.eval a c218 := h 217 (by decide)
  have h22 : Entails.eval a c1836 := derived1836 a h
  have h23 : Entails.eval a c310 := h 309 (by decide)
  have h24 : Entails.eval a c306 := h 305 (by decide)
  have h25 : Entails.eval a c287 := h 286 (by decide)
  have h26 : Entails.eval a c197 := h 196 (by decide)
  have h27 : Entails.eval a c243 := h 242 (by decide)
  have h28 : Entails.eval a c257 := h 256 (by decide)
  have h29 : Entails.eval a c154 := h 153 (by decide)
  have h30 : Entails.eval a c1810 := derived1810 a h
  have h31 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1838 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨46, by decide⟩, true), (⟨38, by decide⟩, false), (⟨43, by decide⟩, true), (⟨37, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c19, some c1779, some c98, some c97, some c1414, some c1671, some c51, some c404, some c1760, some c88, some c95, some c293, some c343, some c358, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1838 : lratChecker f1838 p1838 = .success := by decide +kernel
theorem unsat1838 : Unsatisfiable (PosFin 57) f1838 := by
  apply lratCheckerSound f1838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1838
  · intro a ha; simp [p1838] at ha; subst a; trivial
  · exact checked1838
theorem derived1838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1838 := by
  apply localUnsat_implies_entails f1838 [c1832, c19, c1779, c98, c97, c1414, c1671, c51, c404, c1760, c88, c95, c293, c343, c358] c1838 unsat1838 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c1414 := derived1414 a h
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c404 := derived404 a h
  have h9 : Entails.eval a c1760 := derived1760 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c343 := h 342 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1839 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1835, some c195, some c234, some c372, some c1832, some c97, some c1671, some c1837, some c56, some c34, some c236, some c19, some c1779, some c98, some c1414, some c272, some c346, some c327, some c209, some c1838, some c280, some c66, some c296, some c95, some c1760, some c206, some c759, some c243, some c324, some c340, some c154, some c1226, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1839 : lratChecker f1839 p1839 = .success := by decide +kernel
theorem unsat1839 : Unsatisfiable (PosFin 57) f1839 := by
  apply lratCheckerSound f1839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1839
  · intro a ha; simp [p1839] at ha; subst a; trivial
  · exact checked1839
theorem derived1839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1839 := by
  apply localUnsat_implies_entails f1839 [c1835, c195, c234, c372, c1832, c97, c1671, c1837, c56, c34, c236, c19, c1779, c98, c1414, c272, c346, c327, c209, c1838, c280, c66, c296, c95, c1760, c206, c759, c243, c324, c340, c154, c1226] c1839 unsat1839 (by rfl) a
  have h0 : Entails.eval a c1835 := derived1835 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c1832 := derived1832 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c1837 := derived1837 a h
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c1779 := derived1779 a h
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c1414 := derived1414 a h
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c346 := h 345 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c1838 := derived1838 a h
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c95 := h 94 (by decide)
  have h24 : Entails.eval a c1760 := derived1760 a h
  have h25 : Entails.eval a c206 := h 205 (by decide)
  have h26 : Entails.eval a c759 := derived759 a h
  have h27 : Entails.eval a c243 := h 242 (by decide)
  have h28 : Entails.eval a c324 := h 323 (by decide)
  have h29 : Entails.eval a c340 := h 339 (by decide)
  have h30 : Entails.eval a c154 := h 153 (by decide)
  have h31 : Entails.eval a c1226 := derived1226 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1840 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c97, some c1671, some c1837, some c56, some c34, some c1835, some c195, some c236, some c19, some c1779, some c98, some c1414, some c372, some c234, some c1839, some c1758, some c310, some c1760, some c404, some c1836, some c88, some c95, some c293, some c295, some c841, some c605, some c1781, some c1783, some c157, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1840 : lratChecker f1840 p1840 = .success := by decide +kernel
theorem unsat1840 : Unsatisfiable (PosFin 57) f1840 := by
  apply lratCheckerSound f1840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1840
  · intro a ha; simp [p1840] at ha; subst a; trivial
  · exact checked1840
theorem derived1840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1840 := by
  apply localUnsat_implies_entails f1840 [c1832, c97, c1671, c1837, c56, c34, c1835, c195, c236, c19, c1779, c98, c1414, c372, c234, c1839, c1758, c310, c1760, c404, c1836, c88, c95, c293, c295, c841, c605, c1781, c1783, c157] c1840 unsat1840 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1837 := derived1837 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c1835 := derived1835 a h
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1779 := derived1779 a h
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c1414 := derived1414 a h
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c234 := h 233 (by decide)
  have h15 : Entails.eval a c1839 := derived1839 a h
  have h16 : Entails.eval a c1758 := derived1758 a h
  have h17 : Entails.eval a c310 := h 309 (by decide)
  have h18 : Entails.eval a c1760 := derived1760 a h
  have h19 : Entails.eval a c404 := derived404 a h
  have h20 : Entails.eval a c1836 := derived1836 a h
  have h21 : Entails.eval a c88 := h 87 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  have h23 : Entails.eval a c293 := h 292 (by decide)
  have h24 : Entails.eval a c295 := h 294 (by decide)
  have h25 : Entails.eval a c841 := derived841 a h
  have h26 : Entails.eval a c605 := derived605 a h
  have h27 : Entails.eval a c1781 := derived1781 a h
  have h28 : Entails.eval a c1783 := derived1783 a h
  have h29 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1841 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1835, some c195, some c236, some c1832, some c19, some c1779, some c98, some c97, some c1414, some c1671, some c1837, some c34, some c56, some c1840, some c76, some c69, some c280, some c1004, some c404, some c1760, some c277, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1841 : lratChecker f1841 p1841 = .success := by decide +kernel
theorem unsat1841 : Unsatisfiable (PosFin 57) f1841 := by
  apply lratCheckerSound f1841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1841
  · intro a ha; simp [p1841] at ha; subst a; trivial
  · exact checked1841
theorem derived1841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1841 := by
  apply localUnsat_implies_entails f1841 [c1835, c195, c236, c1832, c19, c1779, c98, c97, c1414, c1671, c1837, c34, c56, c1840, c76, c69, c280, c1004, c404, c1760, c277] c1841 unsat1841 (by rfl) a
  have h0 : Entails.eval a c1835 := derived1835 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c1832 := derived1832 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c1779 := derived1779 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c1837 := derived1837 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c1840 := derived1840 a h
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c1004 := derived1004 a h
  have h18 : Entails.eval a c404 := derived404 a h
  have h19 : Entails.eval a c1760 := derived1760 a h
  have h20 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1842 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨34, by decide⟩, false), (⟨21, by decide⟩, true), (⟨43, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c202, some c1760, some c27, some c88, some c67, some c333, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1842 : lratChecker f1842 p1842 = .success := by decide +kernel
theorem unsat1842 : Unsatisfiable (PosFin 57) f1842 := by
  apply lratCheckerSound f1842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1842
  · intro a ha; simp [p1842] at ha; subst a; trivial
  · exact checked1842
theorem derived1842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1842 := by
  apply localUnsat_implies_entails f1842 [c206, c202, c1760, c27, c88, c67, c333] c1842 unsat1842 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c1760 := derived1760 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1843 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨27, by decide⟩, true), (⟨20, by decide⟩, false), (⟨32, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c310, some c306, some c197, some c198, some c256, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1843 : lratChecker f1843 p1843 = .success := by decide +kernel
theorem unsat1843 : Unsatisfiable (PosFin 57) f1843 := by
  apply lratCheckerSound f1843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1843
  · intro a ha; simp [p1843] at ha; subst a; trivial
  · exact checked1843
theorem derived1843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1843 := by
  apply localUnsat_implies_entails f1843 [c310, c306, c197, c198, c256] c1843 unsat1843 (by rfl) a
  have h0 : Entails.eval a c310 := h 309 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1844 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨23, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c19, some c1779, some c98, some c97, some c1414, some c1671, some c372, some c234, some c206, some c1842, some c1760, some c34, some c88, some c95, some c296, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1844 : lratChecker f1844 p1844 = .success := by decide +kernel
theorem unsat1844 : Unsatisfiable (PosFin 57) f1844 := by
  apply lratCheckerSound f1844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1844
  · intro a ha; simp [p1844] at ha; subst a; trivial
  · exact checked1844
theorem derived1844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1844 := by
  apply localUnsat_implies_entails f1844 [c1832, c19, c1779, c98, c97, c1414, c1671, c372, c234, c206, c1842, c1760, c34, c88, c95, c296] c1844 unsat1844 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c1414 := derived1414 a h
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c234 := h 233 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c1842 := derived1842 a h
  have h11 : Entails.eval a c1760 := derived1760 a h
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c95 := h 94 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1845 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c97, some c1779, some c98, some c1671, some c1835, some c195, some c19, some c236, some c1841, some c40, some c63, some c412, some c351, some c268, some c61, some c217, some c413, some c29, some c1843, some c202, some c27, some c1844, some c231, some c67, some c69, some c338, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1845 : lratChecker f1845 p1845 = .success := by decide +kernel
theorem unsat1845 : Unsatisfiable (PosFin 57) f1845 := by
  apply lratCheckerSound f1845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1845
  · intro a ha; simp [p1845] at ha; subst a; trivial
  · exact checked1845
theorem derived1845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1845 := by
  apply localUnsat_implies_entails f1845 [c1832, c97, c1779, c98, c1671, c1835, c195, c19, c236, c1841, c40, c63, c412, c351, c268, c61, c217, c413, c29, c1843, c202, c27, c1844, c231, c67, c69, c338] c1845 unsat1845 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1835 := derived1835 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c1841 := derived1841 a h
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c412 := derived412 a h
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  have h17 : Entails.eval a c413 := derived413 a h
  have h18 : Entails.eval a c29 := h 28 (by decide)
  have h19 : Entails.eval a c1843 := derived1843 a h
  have h20 : Entails.eval a c202 := h 201 (by decide)
  have h21 : Entails.eval a c27 := h 26 (by decide)
  have h22 : Entails.eval a c1844 := derived1844 a h
  have h23 : Entails.eval a c231 := h 230 (by decide)
  have h24 : Entails.eval a c67 := h 66 (by decide)
  have h25 : Entails.eval a c69 := h 68 (by decide)
  have h26 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1846 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨50, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨43, by decide⟩, true), (⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c88, some c329, some c986, some c149, some c354, some c173, some c136, some c968, some c163, some c176, some c184, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1846 : lratChecker f1846 p1846 = .success := by decide +kernel
theorem unsat1846 : Unsatisfiable (PosFin 57) f1846 := by
  apply lratCheckerSound f1846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1846
  · intro a ha; simp [p1846] at ha; subst a; trivial
  · exact checked1846
theorem derived1846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1846 := by
  apply localUnsat_implies_entails f1846 [c88, c329, c986, c149, c354, c173, c136, c968, c163, c176, c184] c1846 unsat1846 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c329 := h 328 (by decide)
  have h2 : Entails.eval a c986 := derived986 a h
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c173 := h 172 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c968 := derived968 a h
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1847 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨40, by decide⟩, false), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c97, some c1779, some c98, some c83, some c372, some c72, some c841, some c1414, some c1671, some c286, some c418, some c44, some c37, some c1758, some c307, some c296, some c88, some c1846, some c189, some c19, some c18, some c206, some c237, some c986, some c149, some c116, some c2, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1847 : lratChecker f1847 p1847 = .success := by decide +kernel
theorem unsat1847 : Unsatisfiable (PosFin 57) f1847 := by
  apply lratCheckerSound f1847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1847
  · intro a ha; simp [p1847] at ha; subst a; trivial
  · exact checked1847
theorem derived1847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1847 := by
  apply localUnsat_implies_entails f1847 [c1832, c97, c1779, c98, c83, c372, c72, c841, c1414, c1671, c286, c418, c44, c37, c1758, c307, c296, c88, c1846, c189, c19, c18, c206, c237, c986, c149, c116, c2] c1847 unsat1847 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c418 := derived418 a h
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c1758 := derived1758 a h
  have h15 : Entails.eval a c307 := h 306 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c1846 := derived1846 a h
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c18 := h 17 (by decide)
  have h22 : Entails.eval a c206 := h 205 (by decide)
  have h23 : Entails.eval a c237 := h 236 (by decide)
  have h24 : Entails.eval a c986 := derived986 a h
  have h25 : Entails.eval a c149 := h 148 (by decide)
  have h26 : Entails.eval a c116 := h 115 (by decide)
  have h27 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1848 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c72, some c1832, some c97, some c1671, some c88, some c378, some c83, some c372, some c841, some c1414, some c180, some c178, some c3, some c955, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1848 : lratChecker f1848 p1848 = .success := by decide +kernel
theorem unsat1848 : Unsatisfiable (PosFin 57) f1848 := by
  apply lratCheckerSound f1848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1848
  · intro a ha; simp [p1848] at ha; subst a; trivial
  · exact checked1848
theorem derived1848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1848 := by
  apply localUnsat_implies_entails f1848 [c1779, c98, c72, c1832, c97, c1671, c88, c378, c83, c372, c841, c1414, c180, c178, c3, c955] c1848 unsat1848 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c1832 := derived1832 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c841 := derived841 a h
  have h11 : Entails.eval a c1414 := derived1414 a h
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c955 := derived955 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1849 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c195, some c19, some c97, some c1779, some c98, some c1845, some c83, some c372, some c1414, some c1745, some c1760, some c81, some c1848, some c2, some c13, some c159, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1849 : lratChecker f1849 p1849 = .success := by decide +kernel
theorem unsat1849 : Unsatisfiable (PosFin 57) f1849 := by
  apply lratCheckerSound f1849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1849
  · intro a ha; simp [p1849] at ha; subst a; trivial
  · exact checked1849
theorem derived1849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1849 := by
  apply localUnsat_implies_entails f1849 [c1832, c195, c19, c97, c1779, c98, c1845, c83, c372, c1414, c1745, c1760, c81, c1848, c2, c13, c159] c1849 unsat1849 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1845 := derived1845 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c1414 := derived1414 a h
  have h10 : Entails.eval a c1745 := derived1745 a h
  have h11 : Entails.eval a c1760 := derived1760 a h
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c1848 := derived1848 a h
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1850 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1832, some c97, some c1414, some c986, some c149, some c180, some c2, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1850 : lratChecker f1850 p1850 = .success := by decide +kernel
theorem unsat1850 : Unsatisfiable (PosFin 57) f1850 := by
  apply lratCheckerSound f1850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1850
  · intro a ha; simp [p1850] at ha; subst a; trivial
  · exact checked1850
theorem derived1850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1850 := by
  apply localUnsat_implies_entails f1850 [c1779, c98, c1832, c97, c1414, c986, c149, c180, c2] c1850 unsat1850 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1832 := derived1832 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c1414 := derived1414 a h
  have h5 : Entails.eval a c986 := derived986 a h
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c180 := h 179 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1851 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c97, some c1779, some c98, some c1845, some c83, some c1847, some c195, some c234, some c19, some c72, some c841, some c1671, some c51, some c1849, some c1759, some c774, some c218, some c1836, some c251, some c1850, some c332, some c1078, some c189, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1851 : lratChecker f1851 p1851 = .success := by decide +kernel
theorem unsat1851 : Unsatisfiable (PosFin 57) f1851 := by
  apply lratCheckerSound f1851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1851
  · intro a ha; simp [p1851] at ha; subst a; trivial
  · exact checked1851
theorem derived1851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1851 := by
  apply localUnsat_implies_entails f1851 [c1832, c97, c1779, c98, c1845, c83, c1847, c195, c234, c19, c72, c841, c1671, c51, c1849, c1759, c774, c218, c1836, c251, c1850, c332, c1078, c189] c1851 unsat1851 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1845 := derived1845 a h
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c1847 := derived1847 a h
  have h7 : Entails.eval a c195 := h 194 (by decide)
  have h8 : Entails.eval a c234 := h 233 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c841 := derived841 a h
  have h12 : Entails.eval a c1671 := derived1671 a h
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c1849 := derived1849 a h
  have h15 : Entails.eval a c1759 := derived1759 a h
  have h16 : Entails.eval a c774 := derived774 a h
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c1836 := derived1836 a h
  have h19 : Entails.eval a c251 := h 250 (by decide)
  have h20 : Entails.eval a c1850 := derived1850 a h
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c1078 := derived1078 a h
  have h23 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1852 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1851, some c1845, some c1779, some c98, some c1832, some c97, some c83, some c372, some c79, some c1847, some c195, some c27, some c234, some c19, some c72, some c841, some c1414, some c1671, some c1849, some c44, some c1758, some c206, some c296, some c272, some c759, some c1846, some c351, some c210, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1852 : lratChecker f1852 p1852 = .success := by decide +kernel
theorem unsat1852 : Unsatisfiable (PosFin 57) f1852 := by
  apply lratCheckerSound f1852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1852
  · intro a ha; simp [p1852] at ha; subst a; trivial
  · exact checked1852
theorem derived1852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1852 := by
  apply localUnsat_implies_entails f1852 [c1851, c1845, c1779, c98, c1832, c97, c83, c372, c79, c1847, c195, c27, c234, c19, c72, c841, c1414, c1671, c1849, c44, c1758, c206, c296, c272, c759, c1846, c351, c210] c1852 unsat1852 (by rfl) a
  have h0 : Entails.eval a c1851 := derived1851 a h
  have h1 : Entails.eval a c1845 := derived1845 a h
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1832 := derived1832 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c1847 := derived1847 a h
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c234 := h 233 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c841 := derived841 a h
  have h16 : Entails.eval a c1414 := derived1414 a h
  have h17 : Entails.eval a c1671 := derived1671 a h
  have h18 : Entails.eval a c1849 := derived1849 a h
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c1758 := derived1758 a h
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c272 := h 271 (by decide)
  have h24 : Entails.eval a c759 := derived759 a h
  have h25 : Entails.eval a c1846 := derived1846 a h
  have h26 : Entails.eval a c351 := h 350 (by decide)
  have h27 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1853 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1845, some c72, some c841, some c1832, some c97, some c1671, some c1847, some c195, some c19, some c1851, some c1852, some c1759, some c774, some c272, some c306, some c303, some c189, some c1850, some c1079, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1853 : lratChecker f1853 p1853 = .success := by decide +kernel
theorem unsat1853 : Unsatisfiable (PosFin 57) f1853 := by
  apply lratCheckerSound f1853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1853
  · intro a ha; simp [p1853] at ha; subst a; trivial
  · exact checked1853
theorem derived1853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1853 := by
  apply localUnsat_implies_entails f1853 [c1779, c98, c1845, c72, c841, c1832, c97, c1671, c1847, c195, c19, c1851, c1852, c1759, c774, c272, c306, c303, c189, c1850, c1079] c1853 unsat1853 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1845 := derived1845 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c1832 := derived1832 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c1847 := derived1847 a h
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c1851 := derived1851 a h
  have h12 : Entails.eval a c1852 := derived1852 a h
  have h13 : Entails.eval a c1759 := derived1759 a h
  have h14 : Entails.eval a c774 := derived774 a h
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c306 := h 305 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c1850 := derived1850 a h
  have h20 : Entails.eval a c1079 := derived1079 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1854 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨26, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1853, some c40, some c1845, some c72, some c296, some c1832, some c97, some c83, some c372, some c79, some c841, some c1414, some c1671, some c986, some c354, some c1850, some c173, some c968, some c124, some c355, some c176, some c163, some c1625, some c9, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1854 : lratChecker f1854 p1854 = .success := by decide +kernel
theorem unsat1854 : Unsatisfiable (PosFin 57) f1854 := by
  apply lratCheckerSound f1854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1854
  · intro a ha; simp [p1854] at ha; subst a; trivial
  · exact checked1854
theorem derived1854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1854 := by
  apply localUnsat_implies_entails f1854 [c1779, c98, c1853, c40, c1845, c72, c296, c1832, c97, c83, c372, c79, c841, c1414, c1671, c986, c354, c1850, c173, c968, c124, c355, c176, c163, c1625, c9] c1854 unsat1854 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1853 := derived1853 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1845 := derived1845 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c1832 := derived1832 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c841 := derived841 a h
  have h13 : Entails.eval a c1414 := derived1414 a h
  have h14 : Entails.eval a c1671 := derived1671 a h
  have h15 : Entails.eval a c986 := derived986 a h
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c1850 := derived1850 a h
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c968 := derived968 a h
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c355 := h 354 (by decide)
  have h22 : Entails.eval a c176 := h 175 (by decide)
  have h23 : Entails.eval a c163 := h 162 (by decide)
  have h24 : Entails.eval a c1625 := derived1625 a h
  have h25 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1855 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1853, some c40, some c1832, some c97, some c1845, some c83, some c72, some c1671, some c286, some c307, some c44, some c1758, some c296, some c88, some c1854, some c1079, some c189, some c18, some c237, some c206, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1855 : lratChecker f1855 p1855 = .success := by decide +kernel
theorem unsat1855 : Unsatisfiable (PosFin 57) f1855 := by
  apply lratCheckerSound f1855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1855
  · intro a ha; simp [p1855] at ha; subst a; trivial
  · exact checked1855
theorem derived1855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1855 := by
  apply localUnsat_implies_entails f1855 [c1779, c98, c1853, c40, c1832, c97, c1845, c83, c72, c1671, c286, c307, c44, c1758, c296, c88, c1854, c1079, c189, c18, c237, c206] c1855 unsat1855 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1853 := derived1853 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c1832 := derived1832 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c1845 := derived1845 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1671 := derived1671 a h
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c1758 := derived1758 a h
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c1854 := derived1854 a h
  have h17 : Entails.eval a c1079 := derived1079 a h
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1856 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1832, some c97, some c1779, some c98, some c1671, some c1845, some c72, some c1853, some c40, some c63, some c1855, some c195, some c1849, some c19, some c44, some c296, some c1854, some c88, some c1079, some c1078, some c189, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1856 : lratChecker f1856 p1856 = .success := by decide +kernel
theorem unsat1856 : Unsatisfiable (PosFin 57) f1856 := by
  apply lratCheckerSound f1856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1856
  · intro a ha; simp [p1856] at ha; subst a; trivial
  · exact checked1856
theorem derived1856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1856 := by
  apply localUnsat_implies_entails f1856 [c1832, c97, c1779, c98, c1671, c1845, c72, c1853, c40, c63, c1855, c195, c1849, c19, c44, c296, c1854, c88, c1079, c1078, c189] c1856 unsat1856 (by rfl) a
  have h0 : Entails.eval a c1832 := derived1832 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c1779 := derived1779 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c1845 := derived1845 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c1853 := derived1853 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c1855 := derived1855 a h
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c1849 := derived1849 a h
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  have h16 : Entails.eval a c1854 := derived1854 a h
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c1079 := derived1079 a h
  have h19 : Entails.eval a c1078 := derived1078 a h
  have h20 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1857 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1856, some c1832, some c97, some c1779, some c98, some c1806, some c1847, some c83, some c63, some c326, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1857 : lratChecker f1857 p1857 = .success := by decide +kernel
theorem unsat1857 : Unsatisfiable (PosFin 57) f1857 := by
  apply lratCheckerSound f1857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1857
  · intro a ha; simp [p1857] at ha; subst a; trivial
  · exact checked1857
theorem derived1857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1857 := by
  apply localUnsat_implies_entails f1857 [c1856, c1832, c97, c1779, c98, c1806, c1847, c83, c63, c326] c1857 unsat1857 (by rfl) a
  have h0 : Entails.eval a c1856 := derived1856 a h
  have h1 : Entails.eval a c1832 := derived1832 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1806 := derived1806 a h
  have h6 : Entails.eval a c1847 := derived1847 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1858 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1856, some c328, some c72, some c1832, some c97, some c1671, some c83, some c326, some c56, some c336, some c372, some c79, some c841, some c1414, some c986, some c354, some c1850, some c173, some c968, some c140, some c355, some c176, some c163, some c1625, some c9, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1858 : lratChecker f1858 p1858 = .success := by decide +kernel
theorem unsat1858 : Unsatisfiable (PosFin 57) f1858 := by
  apply lratCheckerSound f1858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1858
  · intro a ha; simp [p1858] at ha; subst a; trivial
  · exact checked1858
theorem derived1858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1858 := by
  apply localUnsat_implies_entails f1858 [c1779, c98, c1856, c328, c72, c1832, c97, c1671, c83, c326, c56, c336, c372, c79, c841, c1414, c986, c354, c1850, c173, c968, c140, c355, c176, c163, c1625, c9] c1858 unsat1858 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1856 := derived1856 a h
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c1832 := derived1832 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c1414 := derived1414 a h
  have h16 : Entails.eval a c986 := derived986 a h
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c1850 := derived1850 a h
  have h19 : Entails.eval a c173 := h 172 (by decide)
  have h20 : Entails.eval a c968 := derived968 a h
  have h21 : Entails.eval a c140 := h 139 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c176 := h 175 (by decide)
  have h24 : Entails.eval a c163 := h 162 (by decide)
  have h25 : Entails.eval a c1625 := derived1625 a h
  have h26 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1859 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1856, some c1832, some c97, some c1779, some c98, some c1671, some c328, some c347, some c72, some c83, some c326, some c1759, some c774, some c1858, some c1078, some c189, some c18, some c237, some c218, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1859 : lratChecker f1859 p1859 = .success := by decide +kernel
theorem unsat1859 : Unsatisfiable (PosFin 57) f1859 := by
  apply lratCheckerSound f1859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1859
  · intro a ha; simp [p1859] at ha; subst a; trivial
  · exact checked1859
theorem derived1859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1859 := by
  apply localUnsat_implies_entails f1859 [c1856, c1832, c97, c1779, c98, c1671, c328, c347, c72, c83, c326, c1759, c774, c1858, c1078, c189, c18, c237, c218] c1859 unsat1859 (by rfl) a
  have h0 : Entails.eval a c1856 := derived1856 a h
  have h1 : Entails.eval a c1832 := derived1832 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c1671 := derived1671 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c347 := h 346 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c1759 := derived1759 a h
  have h12 : Entails.eval a c774 := derived774 a h
  have h13 : Entails.eval a c1858 := derived1858 a h
  have h14 : Entails.eval a c1078 := derived1078 a h
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c237 := h 236 (by decide)
  have h18 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1860 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1671, some c1832, some c97, some c1414, some c1856, some c1857, some c1859, some c40, some c63, some c326, some c352, some c345, some c76, some c83, some c69, some c59, some c963, some c280, some c1004, some c34, some c201, some c228, some c215, some c256, some c1080, some c217, some c204, some c868, some c413, some c355, some c262, some c289, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1860 : lratChecker f1860 p1860 = .success := by decide +kernel
theorem unsat1860 : Unsatisfiable (PosFin 57) f1860 := by
  apply lratCheckerSound f1860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1860
  · intro a ha; simp [p1860] at ha; subst a; trivial
  · exact checked1860
theorem derived1860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1860 := by
  apply localUnsat_implies_entails f1860 [c1779, c98, c1671, c1832, c97, c1414, c1856, c1857, c1859, c40, c63, c326, c352, c345, c76, c83, c69, c59, c963, c280, c1004, c34, c201, c228, c215, c256, c1080, c217, c204, c868, c413, c355, c262, c289] c1860 unsat1860 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1671 := derived1671 a h
  have h3 : Entails.eval a c1832 := derived1832 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c1414 := derived1414 a h
  have h6 : Entails.eval a c1856 := derived1856 a h
  have h7 : Entails.eval a c1857 := derived1857 a h
  have h8 : Entails.eval a c1859 := derived1859 a h
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c963 := derived963 a h
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c1004 := derived1004 a h
  have h21 : Entails.eval a c34 := h 33 (by decide)
  have h22 : Entails.eval a c201 := h 200 (by decide)
  have h23 : Entails.eval a c228 := h 227 (by decide)
  have h24 : Entails.eval a c215 := h 214 (by decide)
  have h25 : Entails.eval a c256 := h 255 (by decide)
  have h26 : Entails.eval a c1080 := derived1080 a h
  have h27 : Entails.eval a c217 := h 216 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c868 := derived868 a h
  have h30 : Entails.eval a c413 := derived413 a h
  have h31 : Entails.eval a c355 := h 354 (by decide)
  have h32 : Entails.eval a c262 := h 261 (by decide)
  have h33 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1861 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1860, some c71, some c841, some c72, some c1671, some c77, some c80, some c1256, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1861 : lratChecker f1861 p1861 = .success := by decide +kernel
theorem unsat1861 : Unsatisfiable (PosFin 57) f1861 := by
  apply lratCheckerSound f1861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1861
  · intro a ha; simp [p1861] at ha; subst a; trivial
  · exact checked1861
theorem derived1861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1861 := by
  apply localUnsat_implies_entails f1861 [c1779, c98, c1860, c71, c841, c72, c1671, c77, c80, c1256] c1861 unsat1861 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c841 := derived841 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c1256 := derived1256 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1862 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨36, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c197, some c198, some c228, some c256, some c217, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p1862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1862 : lratChecker f1862 p1862 = .success := by decide +kernel
theorem unsat1862 : Unsatisfiable (PosFin 57) f1862 := by
  apply lratCheckerSound f1862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1862
  · intro a ha; simp [p1862] at ha; subst a; trivial
  · exact checked1862
theorem derived1862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1862 := by
  apply localUnsat_implies_entails f1862 [c197, c198, c228, c256, c217] c1862 unsat1862 (by rfl) a
  have h0 : Entails.eval a c197 := h 196 (by decide)
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1863 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c179, some c114, some c131, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1863 : lratChecker f1863 p1863 = .success := by decide +kernel
theorem unsat1863 : Unsatisfiable (PosFin 57) f1863 := by
  apply lratCheckerSound f1863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1863
  · intro a ha; simp [p1863] at ha; subst a; trivial
  · exact checked1863
theorem derived1863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1863 := by
  apply localUnsat_implies_entails f1863 [c179, c114, c131] c1863 unsat1863 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1864 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨53, by decide⟩, true), (⟨36, by decide⟩, true), (⟨43, by decide⟩, true), (⟨32, by decide⟩, false), (⟨40, by decide⟩, true), (⟨48, by decide⟩, false), (⟨56, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c370, some c206, some c200, some c228, some c217, some c256, some c226, some c1863, some c1491, some c162, some c111, some c131, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1864 : lratChecker f1864 p1864 = .success := by decide +kernel
theorem unsat1864 : Unsatisfiable (PosFin 57) f1864 := by
  apply lratCheckerSound f1864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1864
  · intro a ha; simp [p1864] at ha; subst a; trivial
  · exact checked1864
theorem derived1864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1864 := by
  apply localUnsat_implies_entails f1864 [c280, c370, c206, c200, c228, c217, c256, c226, c1863, c1491, c162, c111, c131] c1864 unsat1864 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c217 := h 216 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c1863 := derived1863 a h
  have h9 : Entails.eval a c1491 := derived1491 a h
  have h10 : Entails.eval a c162 := h 161 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1865 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨38, by decide⟩, false), (⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c2, some c139, some c158, some c172, some c142, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1865 : lratChecker f1865 p1865 = .success := by decide +kernel
theorem unsat1865 : Unsatisfiable (PosFin 57) f1865 := by
  apply lratCheckerSound f1865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1865
  · intro a ha; simp [p1865] at ha; subst a; trivial
  · exact checked1865
theorem derived1865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1865 := by
  apply localUnsat_implies_entails f1865 [c1779, c2, c139, c158, c172, c142] c1865 unsat1865 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1866 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c168, some c162, some c114, some c188, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1866 : lratChecker f1866 p1866 = .success := by decide +kernel
theorem unsat1866 : Unsatisfiable (PosFin 57) f1866 := by
  apply lratCheckerSound f1866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1866
  · intro a ha; simp [p1866] at ha; subst a; trivial
  · exact checked1866
theorem derived1866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1866 := by
  apply localUnsat_implies_entails f1866 [c168, c162, c114, c188] c1866 unsat1866 (by rfl) a
  have h0 : Entails.eval a c168 := h 167 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1867 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨55, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c2, some c18, some c1865, some c149, some c220, some c239, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1867 : lratChecker f1867 p1867 = .success := by decide +kernel
theorem unsat1867 : Unsatisfiable (PosFin 57) f1867 := by
  apply lratCheckerSound f1867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1867
  · intro a ha; simp [p1867] at ha; subst a; trivial
  · exact checked1867
theorem derived1867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1867 := by
  apply localUnsat_implies_entails f1867 [c1779, c2, c18, c1865, c149, c220, c239] c1867 unsat1867 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c1865 := derived1865 a h
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1868 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, true), (⟨32, by decide⟩, false), (⟨31, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c130, some c132, some c179, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1868 : lratChecker f1868 p1868 = .success := by decide +kernel
theorem unsat1868 : Unsatisfiable (PosFin 57) f1868 := by
  apply lratCheckerSound f1868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1868
  · intro a ha; simp [p1868] at ha; subst a; trivial
  · exact checked1868
theorem derived1868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1868 := by
  apply localUnsat_implies_entails f1868 [c130, c132, c179] c1868 unsat1868 (by rfl) a
  have h0 : Entails.eval a c130 := h 129 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1869 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨29, by decide⟩, false), (⟨36, by decide⟩, true), (⟨37, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c284, some c263, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1869 : lratChecker f1869 p1869 = .success := by decide +kernel
theorem unsat1869 : Unsatisfiable (PosFin 57) f1869 := by
  apply lratCheckerSound f1869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1869
  · intro a ha; simp [p1869] at ha; subst a; trivial
  · exact checked1869
theorem derived1869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1869 := by
  apply localUnsat_implies_entails f1869 [c313, c284, c263] c1869 unsat1869 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1870 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨34, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c202, some c139, some c247, some c109, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p1870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1870 : lratChecker f1870 p1870 = .success := by decide +kernel
theorem unsat1870 : Unsatisfiable (PosFin 57) f1870 := by
  apply lratCheckerSound f1870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1870
  · intro a ha; simp [p1870] at ha; subst a; trivial
  · exact checked1870
theorem derived1870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1870 := by
  apply localUnsat_implies_entails f1870 [c194, c202, c139, c247, c109] c1870 unsat1870 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1871 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c98, some c1860, some c97, some c71, some c841, some c72, some c1671, some c77, some c57, some c320, some c1861, some c103, some c59, some c91, some c333, some c39, some c299, some c317, some c40, some c280, some c307, some c370, some c351, some c338, some c1862, some c17, some c18, some c1864, some c1866, some c13, some c1867, some c224, some c217, some c1868, some c164, some c226, some c1869, some c153, some c142, some c1870, some c131, some c177, some c111, some c245, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45]]
theorem checked1871 : lratChecker f1871 p1871 = .success := by decide +kernel
theorem unsat1871 : Unsatisfiable (PosFin 57) f1871 := by
  apply lratCheckerSound f1871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1871
  · intro a ha; simp [p1871] at ha; subst a; trivial
  · exact checked1871
theorem derived1871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1871 := by
  apply localUnsat_implies_entails f1871 [c1779, c98, c1860, c97, c71, c841, c72, c1671, c77, c57, c320, c1861, c103, c59, c91, c333, c39, c299, c317, c40, c280, c307, c370, c351, c338, c1862, c17, c18, c1864, c1866, c13, c1867, c224, c217, c1868, c164, c226, c1869, c153, c142, c1870, c131, c177, c111, c245] c1871 unsat1871 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c1861 := derived1861 a h
  have h12 : Entails.eval a c103 := h 102 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c299 := h 298 (by decide)
  have h18 : Entails.eval a c317 := h 316 (by decide)
  have h19 : Entails.eval a c40 := h 39 (by decide)
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c307 := h 306 (by decide)
  have h22 : Entails.eval a c370 := h 369 (by decide)
  have h23 : Entails.eval a c351 := h 350 (by decide)
  have h24 : Entails.eval a c338 := h 337 (by decide)
  have h25 : Entails.eval a c1862 := derived1862 a h
  have h26 : Entails.eval a c17 := h 16 (by decide)
  have h27 : Entails.eval a c18 := h 17 (by decide)
  have h28 : Entails.eval a c1864 := derived1864 a h
  have h29 : Entails.eval a c1866 := derived1866 a h
  have h30 : Entails.eval a c13 := h 12 (by decide)
  have h31 : Entails.eval a c1867 := derived1867 a h
  have h32 : Entails.eval a c224 := h 223 (by decide)
  have h33 : Entails.eval a c217 := h 216 (by decide)
  have h34 : Entails.eval a c1868 := derived1868 a h
  have h35 : Entails.eval a c164 := h 163 (by decide)
  have h36 : Entails.eval a c226 := h 225 (by decide)
  have h37 : Entails.eval a c1869 := derived1869 a h
  have h38 : Entails.eval a c153 := h 152 (by decide)
  have h39 : Entails.eval a c142 := h 141 (by decide)
  have h40 : Entails.eval a c1870 := derived1870 a h
  have h41 : Entails.eval a c131 := h 130 (by decide)
  have h42 : Entails.eval a c177 := h 176 (by decide)
  have h43 : Entails.eval a c111 := h 110 (by decide)
  have h44 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1872 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1860, some c97, some c77, some c1779, some c98, some c71, some c841, some c72, some c370, some c57, some c39, some c320, some c40, some c307, some c280, some c1861, some c103, some c59, some c91, some c317, some c299, some c1871, some c348, some c380, some c1862, some c17, some c18, some c193, some c219, some c218, some c1866, some c1868, some c255, some c228, some c139, some c109, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1872 : lratChecker f1872 p1872 = .success := by decide +kernel
theorem unsat1872 : Unsatisfiable (PosFin 57) f1872 := by
  apply lratCheckerSound f1872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1872
  · intro a ha; simp [p1872] at ha; subst a; trivial
  · exact checked1872
theorem derived1872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1872 := by
  apply localUnsat_implies_entails f1872 [c1671, c1860, c97, c77, c1779, c98, c71, c841, c72, c370, c57, c39, c320, c40, c307, c280, c1861, c103, c59, c91, c317, c299, c1871, c348, c380, c1862, c17, c18, c193, c219, c218, c1866, c1868, c255, c228, c139, c109] c1872 unsat1872 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c1861 := derived1861 a h
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c59 := h 58 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c299 := h 298 (by decide)
  have h22 : Entails.eval a c1871 := derived1871 a h
  have h23 : Entails.eval a c348 := h 347 (by decide)
  have h24 : Entails.eval a c380 := h 379 (by decide)
  have h25 : Entails.eval a c1862 := derived1862 a h
  have h26 : Entails.eval a c17 := h 16 (by decide)
  have h27 : Entails.eval a c18 := h 17 (by decide)
  have h28 : Entails.eval a c193 := h 192 (by decide)
  have h29 : Entails.eval a c219 := h 218 (by decide)
  have h30 : Entails.eval a c218 := h 217 (by decide)
  have h31 : Entails.eval a c1866 := derived1866 a h
  have h32 : Entails.eval a c1868 := derived1868 a h
  have h33 : Entails.eval a c255 := h 254 (by decide)
  have h34 : Entails.eval a c228 := h 227 (by decide)
  have h35 : Entails.eval a c139 := h 138 (by decide)
  have h36 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1873 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1872, some c1779, some c98, some c1860, some c97, some c71, some c841, some c72, some c1671, some c77, some c40, some c280, some c34, some c1861, some c103, some c59, some c91, some c339, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1873 : lratChecker f1873 p1873 = .success := by decide +kernel
theorem unsat1873 : Unsatisfiable (PosFin 57) f1873 := by
  apply lratCheckerSound f1873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1873
  · intro a ha; simp [p1873] at ha; subst a; trivial
  · exact checked1873
theorem derived1873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1873 := by
  apply localUnsat_implies_entails f1873 [c1872, c1779, c98, c1860, c97, c71, c841, c72, c1671, c77, c40, c280, c34, c1861, c103, c59, c91, c339] c1873 unsat1873 (by rfl) a
  have h0 : Entails.eval a c1872 := derived1872 a h
  have h1 : Entails.eval a c1779 := derived1779 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c1860 := derived1860 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c841 := derived841 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c1861 := derived1861 a h
  have h14 : Entails.eval a c103 := h 102 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1874 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1671, some c1860, some c97, some c77, some c1779, some c98, some c71, some c841, some c72, some c1873, some c320, some c34, some c280, some c80, some c49, some c278, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1874 : lratChecker f1874 p1874 = .success := by decide +kernel
theorem unsat1874 : Unsatisfiable (PosFin 57) f1874 := by
  apply lratCheckerSound f1874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1874
  · intro a ha; simp [p1874] at ha; subst a; trivial
  · exact checked1874
theorem derived1874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1874 := by
  apply localUnsat_implies_entails f1874 [c1671, c1860, c97, c77, c1779, c98, c71, c841, c72, c1873, c320, c34, c280, c80, c49, c278] c1874 unsat1874 (by rfl) a
  have h0 : Entails.eval a c1671 := derived1671 a h
  have h1 : Entails.eval a c1860 := derived1860 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c841 := derived841 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c1873 := derived1873 a h
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1875 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨54, by decide⟩, false), (⟨36, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c341, some c177, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1875 : lratChecker f1875 p1875 = .success := by decide +kernel
theorem unsat1875 : Unsatisfiable (PosFin 57) f1875 := by
  apply lratCheckerSound f1875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1875
  · intro a ha; simp [p1875] at ha; subst a; trivial
  · exact checked1875
theorem derived1875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1875 := by
  apply localUnsat_implies_entails f1875 [c147, c341, c177] c1875 unsat1875 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1876 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨20, by decide⟩, false), (⟨36, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true), (⟨37, by decide⟩, false), (⟨51, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c352, some c841, some c362, some c153, some c146, some c164, some c226, some c1875, some c194, some c214, some c123, some c247, some c109, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1876 : lratChecker f1876 p1876 = .success := by decide +kernel
theorem unsat1876 : Unsatisfiable (PosFin 57) f1876 := by
  apply lratCheckerSound f1876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1876
  · intro a ha; simp [p1876] at ha; subst a; trivial
  · exact checked1876
theorem derived1876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1876 := by
  apply localUnsat_implies_entails f1876 [c342, c352, c841, c362, c153, c146, c164, c226, c1875, c194, c214, c123, c247, c109] c1876 unsat1876 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c841 := derived841 a h
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c1875 := derived1875 a h
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1877 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨53, by decide⟩, true), (⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨56, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c148, some c179, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false))]
def p1877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1877 : lratChecker f1877 p1877 = .success := by decide +kernel
theorem unsat1877 : Unsatisfiable (PosFin 57) f1877 := by
  apply lratCheckerSound f1877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1877
  · intro a ha; simp [p1877] at ha; subst a; trivial
  · exact checked1877
theorem derived1877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1877 := by
  apply localUnsat_implies_entails f1877 [c146, c148, c179] c1877 unsat1877 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1878 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true), (⟨37, by decide⟩, false), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨51, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c841, some c342, some c1877, some c164, some c352, some c324, some c362, some c1876, some c1875, some c204, some c214, some c247, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p1878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1878 : lratChecker f1878 p1878 = .success := by decide +kernel
theorem unsat1878 : Unsatisfiable (PosFin 57) f1878 := by
  apply lratCheckerSound f1878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1878
  · intro a ha; simp [p1878] at ha; subst a; trivial
  · exact checked1878
theorem derived1878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1878 := by
  apply localUnsat_implies_entails f1878 [c841, c342, c1877, c164, c352, c324, c362, c1876, c1875, c204, c214, c247] c1878 unsat1878 (by rfl) a
  have h0 : Entails.eval a c841 := derived841 a h
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c1877 := derived1877 a h
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c1876 := derived1876 a h
  have h8 : Entails.eval a c1875 := derived1875 a h
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1879 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1779, some c1874, some c1860, some c1671, some c97, some c77, some c98, some c71, some c841, some c72, some c370, some c1873, some c320, some c34, some c280, some c103, some c47, some c277, some c17, some c18, some c1866, some c13, some c2, some c91, some c293, some c495, some c149, some c171, some c186, some c121, some c224, some c245, some c111, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1879 : lratChecker f1879 p1879 = .success := by decide +kernel
theorem unsat1879 : Unsatisfiable (PosFin 57) f1879 := by
  apply lratCheckerSound f1879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1879
  · intro a ha; simp [p1879] at ha; subst a; trivial
  · exact checked1879
theorem derived1879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1879 := by
  apply localUnsat_implies_entails f1879 [c1779, c1874, c1860, c1671, c97, c77, c98, c71, c841, c72, c370, c1873, c320, c34, c280, c103, c47, c277, c17, c18, c1866, c13, c2, c91, c293, c495, c149, c171, c186, c121, c224, c245, c111] c1879 unsat1879 (by rfl) a
  have h0 : Entails.eval a c1779 := derived1779 a h
  have h1 : Entails.eval a c1874 := derived1874 a h
  have h2 : Entails.eval a c1860 := derived1860 a h
  have h3 : Entails.eval a c1671 := derived1671 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c841 := derived841 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c1873 := derived1873 a h
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c1866 := derived1866 a h
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  have h23 : Entails.eval a c91 := h 90 (by decide)
  have h24 : Entails.eval a c293 := h 292 (by decide)
  have h25 : Entails.eval a c495 := derived495 a h
  have h26 : Entails.eval a c149 := h 148 (by decide)
  have h27 : Entails.eval a c171 := h 170 (by decide)
  have h28 : Entails.eval a c186 := h 185 (by decide)
  have h29 : Entails.eval a c121 := h 120 (by decide)
  have h30 : Entails.eval a c224 := h 223 (by decide)
  have h31 : Entails.eval a c245 := h 244 (by decide)
  have h32 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1880 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1860, some c97, some c71, some c841, some c1872, some c1873, some c342, some c1877, some c1671, some c77, some c1779, some c98, some c72, some c320, some c34, some c280, some c1874, some c103, some c47, some c91, some c299, some c308, some c277, some c370, some c17, some c18, some c1866, some c13, some c164, some c1878, some c192, some c226, some c1879, some c239, some c208, some c109, some c123, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked1880 : lratChecker f1880 p1880 = .success := by decide +kernel
theorem unsat1880 : Unsatisfiable (PosFin 57) f1880 := by
  apply lratCheckerSound f1880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1880
  · intro a ha; simp [p1880] at ha; subst a; trivial
  · exact checked1880
theorem derived1880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1880 := by
  apply localUnsat_implies_entails f1880 [c1860, c97, c71, c841, c1872, c1873, c342, c1877, c1671, c77, c1779, c98, c72, c320, c34, c280, c1874, c103, c47, c91, c299, c308, c277, c370, c17, c18, c1866, c13, c164, c1878, c192, c226, c1879, c239, c208, c109, c123] c1880 unsat1880 (by rfl) a
  have h0 : Entails.eval a c1860 := derived1860 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c841 := derived841 a h
  have h4 : Entails.eval a c1872 := derived1872 a h
  have h5 : Entails.eval a c1873 := derived1873 a h
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c1877 := derived1877 a h
  have h8 : Entails.eval a c1671 := derived1671 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c1779 := derived1779 a h
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c320 := h 319 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c1874 := derived1874 a h
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c299 := h 298 (by decide)
  have h21 : Entails.eval a c308 := h 307 (by decide)
  have h22 : Entails.eval a c277 := h 276 (by decide)
  have h23 : Entails.eval a c370 := h 369 (by decide)
  have h24 : Entails.eval a c17 := h 16 (by decide)
  have h25 : Entails.eval a c18 := h 17 (by decide)
  have h26 : Entails.eval a c1866 := derived1866 a h
  have h27 : Entails.eval a c13 := h 12 (by decide)
  have h28 : Entails.eval a c164 := h 163 (by decide)
  have h29 : Entails.eval a c1878 := derived1878 a h
  have h30 : Entails.eval a c192 := h 191 (by decide)
  have h31 : Entails.eval a c226 := h 225 (by decide)
  have h32 : Entails.eval a c1879 := derived1879 a h
  have h33 : Entails.eval a c239 := h 238 (by decide)
  have h34 : Entails.eval a c208 := h 207 (by decide)
  have h35 : Entails.eval a c109 := h 108 (by decide)
  have h36 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1880

end CochromaticTwenty.Certificates.B16_8_2
