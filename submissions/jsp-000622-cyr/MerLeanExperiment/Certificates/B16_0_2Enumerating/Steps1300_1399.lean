import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1200_1299

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1714 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c1632, some c1710, some c2, some c1686, some c266, some c265, some c127, some c199, some c122, some c1711, some c1712, some c1713, some c43, some c107, some c1299, some c1380, some c49, some c212, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1714 : lratChecker f1714 p1714 = .success := by decide +kernel
theorem unsat1714 : Unsatisfiable (PosFin 57) f1714 := by
  apply lratCheckerSound f1714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1714
  · intro a ha; simp [p1714] at ha; subst a; trivial
  · exact checked1714
theorem derived1714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1714 := by
  apply localUnsat_implies_entails f1714 [c115, c1632, c1710, c2, c1686, c266, c265, c127, c199, c122, c1711, c1712, c1713, c43, c107, c1299, c1380, c49, c212] c1714 unsat1714 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1710 := derived1710 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1686 := derived1686 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c1711 := derived1711 a h
  have h11 : Entails.eval a c1712 := derived1712 a h
  have h12 : Entails.eval a c1713 := derived1713 a h
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c1299 := derived1299 a h
  have h16 : Entails.eval a c1380 := derived1380 a h
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1715 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c122, some c1261, some c197, some c1161, some c1004, some c27, some c144, some c279, some c317, some c216, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1715 : lratChecker f1715 p1715 = .success := by decide +kernel
theorem unsat1715 : Unsatisfiable (PosFin 57) f1715 := by
  apply lratCheckerSound f1715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1715
  · intro a ha; simp [p1715] at ha; subst a; trivial
  · exact checked1715
theorem derived1715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1715 := by
  apply localUnsat_implies_entails f1715 [c115, c122, c1261, c197, c1161, c1004, c27, c144, c279, c317, c216] c1715 unsat1715 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c1261 := derived1261 a h
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c1161 := derived1161 a h
  have h5 : Entails.eval a c1004 := derived1004 a h
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c279 := h 278 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1716 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨35, by decide⟩, false), (⟨38, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c261, some c28, some c226, some c168, some c352, some c72, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1716 : lratChecker f1716 p1716 = .success := by decide +kernel
theorem unsat1716 : Unsatisfiable (PosFin 57) f1716 := by
  apply lratCheckerSound f1716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1716
  · intro a ha; simp [p1716] at ha; subst a; trivial
  · exact checked1716
theorem derived1716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1716 := by
  apply localUnsat_implies_entails f1716 [c263, c261, c28, c226, c168, c352, c72] c1716 unsat1716 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1717 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c1147, some c1227, some c222, some c1716, some c27, some c1024, some c168, some c28, some c73, some c1119, some c349, some c58, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1717 : lratChecker f1717 p1717 = .success := by decide +kernel
theorem unsat1717 : Unsatisfiable (PosFin 57) f1717 := by
  apply lratCheckerSound f1717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1717
  · intro a ha; simp [p1717] at ha; subst a; trivial
  · exact checked1717
theorem derived1717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1717 := by
  apply localUnsat_implies_entails f1717 [c111, c1147, c1227, c222, c1716, c27, c1024, c168, c28, c73, c1119, c349, c58] c1717 unsat1717 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1227 := derived1227 a h
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c1716 := derived1716 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c1024 := derived1024 a h
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c1119 := derived1119 a h
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1718 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c197, some c1004, some c144, some c137, some c317, some c77, some c986, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1718 : lratChecker f1718 p1718 = .success := by decide +kernel
theorem unsat1718 : Unsatisfiable (PosFin 57) f1718 := by
  apply lratCheckerSound f1718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1718
  · intro a ha; simp [p1718] at ha; subst a; trivial
  · exact checked1718
theorem derived1718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1718 := by
  apply localUnsat_implies_entails f1718 [c105, c197, c1004, c144, c137, c317, c77, c986] c1718 unsat1718 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c1004 := derived1004 a h
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c986 := derived986 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1719 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨53, by decide⟩, true), (⟨13, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, true), (⟨39, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c528, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1719 : lratChecker f1719 p1719 = .success := by decide +kernel
theorem unsat1719 : Unsatisfiable (PosFin 57) f1719 := by
  apply lratCheckerSound f1719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1719
  · intro a ha; simp [p1719] at ha; subst a; trivial
  · exact checked1719
theorem derived1719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1719 := by
  apply localUnsat_implies_entails f1719 [c351, c528] c1719 unsat1719 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c528 := derived528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1720 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨55, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c27, some c17, some c1147, some c539, some c194, some c1719, some c222, some c343, some c474, some c193, some c60, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1720 : lratChecker f1720 p1720 = .success := by decide +kernel
theorem unsat1720 : Unsatisfiable (PosFin 57) f1720 := by
  apply lratCheckerSound f1720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1720
  · intro a ha; simp [p1720] at ha; subst a; trivial
  · exact checked1720
theorem derived1720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1720 := by
  apply localUnsat_implies_entails f1720 [c27, c17, c1147, c539, c194, c1719, c222, c343, c474, c193, c60] c1720 unsat1720 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c1719 := derived1719 a h
  have h6 : Entails.eval a c222 := h 221 (by decide)
  have h7 : Entails.eval a c343 := h 342 (by decide)
  have h8 : Entails.eval a c474 := derived474 a h
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1721 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1686, some c1710, some c1714, some c105, some c115, some c50, some c1715, some c111, some c1632, some c2, some c1717, some c127, some c263, some c1024, some c1119, some c58, some c97, some c1718, some c1720, some c1192, some c1376, some c151, some c837, some c317, some c216, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1721 : lratChecker f1721 p1721 = .success := by decide +kernel
theorem unsat1721 : Unsatisfiable (PosFin 57) f1721 := by
  apply lratCheckerSound f1721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1721
  · intro a ha; simp [p1721] at ha; subst a; trivial
  · exact checked1721
theorem derived1721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1721 := by
  apply localUnsat_implies_entails f1721 [c1686, c1710, c1714, c105, c115, c50, c1715, c111, c1632, c2, c1717, c127, c263, c1024, c1119, c58, c97, c1718, c1720, c1192, c1376, c151, c837, c317, c216] c1721 unsat1721 (by rfl) a
  have h0 : Entails.eval a c1686 := derived1686 a h
  have h1 : Entails.eval a c1710 := derived1710 a h
  have h2 : Entails.eval a c1714 := derived1714 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c1715 := derived1715 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1632 := derived1632 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c1717 := derived1717 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c1024 := derived1024 a h
  have h14 : Entails.eval a c1119 := derived1119 a h
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c97 := h 96 (by decide)
  have h17 : Entails.eval a c1718 := derived1718 a h
  have h18 : Entails.eval a c1720 := derived1720 a h
  have h19 : Entails.eval a c1192 := derived1192 a h
  have h20 : Entails.eval a c1376 := derived1376 a h
  have h21 : Entails.eval a c151 := h 150 (by decide)
  have h22 : Entails.eval a c837 := derived837 a h
  have h23 : Entails.eval a c317 := h 316 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1722 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1714, some c1147, some c115, some c1710, some c1686, some c1632, some c111, some c105, some c50, some c1715, some c1721, some c106, some c1219, some c1335, some c26, some c1386, some c261, some c127, some c1193, some c167, some c166, some c227, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1722 : lratChecker f1722 p1722 = .success := by decide +kernel
theorem unsat1722 : Unsatisfiable (PosFin 57) f1722 := by
  apply lratCheckerSound f1722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1722
  · intro a ha; simp [p1722] at ha; subst a; trivial
  · exact checked1722
theorem derived1722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1722 := by
  apply localUnsat_implies_entails f1722 [c1714, c1147, c115, c1710, c1686, c1632, c111, c105, c50, c1715, c1721, c106, c1219, c1335, c26, c1386, c261, c127, c1193, c167, c166, c227] c1722 unsat1722 (by rfl) a
  have h0 : Entails.eval a c1714 := derived1714 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1710 := derived1710 a h
  have h4 : Entails.eval a c1686 := derived1686 a h
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c1715 := derived1715 a h
  have h10 : Entails.eval a c1721 := derived1721 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c1335 := derived1335 a h
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c1386 := derived1386 a h
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c1193 := derived1193 a h
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c166 := h 165 (by decide)
  have h21 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1723 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c261, some c39, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1723 : lratChecker f1723 p1723 = .success := by decide +kernel
theorem unsat1723 : Unsatisfiable (PosFin 57) f1723 := by
  apply lratCheckerSound f1723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1723
  · intro a ha; simp [p1723] at ha; subst a; trivial
  · exact checked1723
theorem derived1723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1723 := by
  apply localUnsat_implies_entails f1723 [c263, c261, c39] c1723 unsat1723 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1724 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1686, some c1632, some c12, some c197, some c1723, some c27, some c539, some c68, some c75, some c40, some c351, some c222, some c279, some c273, some c216, some c141, some c42, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1724 : lratChecker f1724 p1724 = .success := by decide +kernel
theorem unsat1724 : Unsatisfiable (PosFin 57) f1724 := by
  apply lratCheckerSound f1724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1724
  · intro a ha; simp [p1724] at ha; subst a; trivial
  · exact checked1724
theorem derived1724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1724 := by
  apply localUnsat_implies_entails f1724 [c1686, c1632, c12, c197, c1723, c27, c539, c68, c75, c40, c351, c222, c279, c273, c216, c141, c42] c1724 unsat1724 (by rfl) a
  have h0 : Entails.eval a c1686 := derived1686 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c1723 := derived1723 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c539 := derived539 a h
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c273 := h 272 (by decide)
  have h14 : Entails.eval a c216 := h 215 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1725 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1219, some c38, some c261, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1725 : lratChecker f1725 p1725 = .success := by decide +kernel
theorem unsat1725 : Unsatisfiable (PosFin 57) f1725 := by
  apply lratCheckerSound f1725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1725
  · intro a ha; simp [p1725] at ha; subst a; trivial
  · exact checked1725
theorem derived1725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1725 := by
  apply localUnsat_implies_entails f1725 [c106, c1219, c38, c261] c1725 unsat1725 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1219 := derived1219 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1726 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1723, some c12, some c197, some c2, some c133, some c141, some c232, some c315, some c317, some c293, some c212, some c234, some c1119, some c96, some c358, some c194, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1726 : lratChecker f1726 p1726 = .success := by decide +kernel
theorem unsat1726 : Unsatisfiable (PosFin 57) f1726 := by
  apply lratCheckerSound f1726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1726
  · intro a ha; simp [p1726] at ha; subst a; trivial
  · exact checked1726
theorem derived1726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1726 := by
  apply localUnsat_implies_entails f1726 [c1723, c12, c197, c2, c133, c141, c232, c315, c317, c293, c212, c234, c1119, c96, c358, c194] c1726 unsat1726 (by rfl) a
  have h0 : Entails.eval a c1723 := derived1723 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c1119 := derived1119 a h
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1727 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1725, some c1723, some c216, some c1147, some c1632, some c2, some c1726, some c42, some c26, some c1229, some c167, some c1119, some c73, some c58, some c350, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1727 : lratChecker f1727 p1727 = .success := by decide +kernel
theorem unsat1727 : Unsatisfiable (PosFin 57) f1727 := by
  apply lratCheckerSound f1727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1727
  · intro a ha; simp [p1727] at ha; subst a; trivial
  · exact checked1727
theorem derived1727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1727 := by
  apply localUnsat_implies_entails f1727 [c1725, c1723, c216, c1147, c1632, c2, c1726, c42, c26, c1229, c167, c1119, c73, c58, c350] c1727 unsat1727 (by rfl) a
  have h0 : Entails.eval a c1725 := derived1725 a h
  have h1 : Entails.eval a c1723 := derived1723 a h
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1726 := derived1726 a h
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1229 := derived1229 a h
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c1119 := derived1119 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1728 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨48, by decide⟩, true), (⟨26, by decide⟩, false), (⟨43, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c301, some c360, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1728 : lratChecker f1728 p1728 = .success := by decide +kernel
theorem unsat1728 : Unsatisfiable (PosFin 57) f1728 := by
  apply lratCheckerSound f1728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1728
  · intro a ha; simp [p1728] at ha; subst a; trivial
  · exact checked1728
theorem derived1728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1728 := by
  apply localUnsat_implies_entails f1728 [c252, c301, c360] c1728 unsat1728 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1729 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1725, some c1723, some c1632, some c12, some c197, some c2, some c1727, some c49, some c212, some c292, some c85, some c234, some c170, some c134, some c232, some c1728, some c541, some c358, some c194, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1729 : lratChecker f1729 p1729 = .success := by decide +kernel
theorem unsat1729 : Unsatisfiable (PosFin 57) f1729 := by
  apply lratCheckerSound f1729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1729
  · intro a ha; simp [p1729] at ha; subst a; trivial
  · exact checked1729
theorem derived1729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1729 := by
  apply localUnsat_implies_entails f1729 [c1725, c1723, c1632, c12, c197, c2, c1727, c49, c212, c292, c85, c234, c170, c134, c232, c1728, c541, c358, c194] c1729 unsat1729 (by rfl) a
  have h0 : Entails.eval a c1725 := derived1725 a h
  have h1 : Entails.eval a c1723 := derived1723 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1727 := derived1727 a h
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c1728 := derived1728 a h
  have h16 : Entails.eval a c541 := derived541 a h
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1730 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨47, by decide⟩, true), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1725, some c1723, some c1147, some c1729, some c28, some c168, some c167, some c228, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1730 : lratChecker f1730 p1730 = .success := by decide +kernel
theorem unsat1730 : Unsatisfiable (PosFin 57) f1730 := by
  apply lratCheckerSound f1730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1730
  · intro a ha; simp [p1730] at ha; subst a; trivial
  · exact checked1730
theorem derived1730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1730 := by
  apply localUnsat_implies_entails f1730 [c1725, c1723, c1147, c1729, c28, c168, c167, c228] c1730 unsat1730 (by rfl) a
  have h0 : Entails.eval a c1725 := derived1725 a h
  have h1 : Entails.eval a c1723 := derived1723 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c1729 := derived1729 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1731 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c236, some c169, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p1731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1731 : lratChecker f1731 p1731 = .success := by decide +kernel
theorem unsat1731 : Unsatisfiable (PosFin 57) f1731 := by
  apply lratCheckerSound f1731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1731
  · intro a ha; simp [p1731] at ha; subst a; trivial
  · exact checked1731
theorem derived1731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1731 := by
  apply localUnsat_implies_entails f1731 [c232, c236, c169] c1731 unsat1731 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c236 := h 235 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1732 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1710, some c2, some c1686, some c115, some c1714, some c1722, some c12, some c197, some c122, some c1725, some c1723, some c1724, some c51, some c1427, some c216, some c1730, some c127, some c1731, some c140, some c313, some c317, some c141, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1732 : lratChecker f1732 p1732 = .success := by decide +kernel
theorem unsat1732 : Unsatisfiable (PosFin 57) f1732 := by
  apply lratCheckerSound f1732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1732
  · intro a ha; simp [p1732] at ha; subst a; trivial
  · exact checked1732
theorem derived1732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1732 := by
  apply localUnsat_implies_entails f1732 [c1632, c1710, c2, c1686, c115, c1714, c1722, c12, c197, c122, c1725, c1723, c1724, c51, c1427, c216, c1730, c127, c1731, c140, c313, c317, c141] c1732 unsat1732 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1710 := derived1710 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1686 := derived1686 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c1714 := derived1714 a h
  have h6 : Entails.eval a c1722 := derived1722 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c1725 := derived1725 a h
  have h11 : Entails.eval a c1723 := derived1723 a h
  have h12 : Entails.eval a c1724 := derived1724 a h
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c1427 := derived1427 a h
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c1730 := derived1730 a h
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c1731 := derived1731 a h
  have h19 : Entails.eval a c140 := h 139 (by decide)
  have h20 : Entails.eval a c313 := h 312 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1733 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1710, some c1686, some c1732, some c204, some c12, some c105, some c111, some c2, some c266, some c265, some c1299, some c4, some c24, some c106, some c161, some c223, some c218, some c348, some c347, some c76, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1733 : lratChecker f1733 p1733 = .success := by decide +kernel
theorem unsat1733 : Unsatisfiable (PosFin 57) f1733 := by
  apply lratCheckerSound f1733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1733
  · intro a ha; simp [p1733] at ha; subst a; trivial
  · exact checked1733
theorem derived1733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1733 := by
  apply localUnsat_implies_entails f1733 [c1632, c1710, c1686, c1732, c204, c12, c105, c111, c2, c266, c265, c1299, c4, c24, c106, c161, c223, c218, c348, c347, c76] c1733 unsat1733 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1710 := derived1710 a h
  have h2 : Entails.eval a c1686 := derived1686 a h
  have h3 : Entails.eval a c1732 := derived1732 a h
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c1299 := derived1299 a h
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c161 := h 160 (by decide)
  have h16 : Entails.eval a c223 := h 222 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c347 := h 346 (by decide)
  have h20 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1734 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1710, some c1686, some c1732, some c204, some c12, some c105, some c111, some c2, some c1733, some c1147, some c1216, some c1219, some c27, some c1100, some c163, some c1227, some c218, some c1709, some c348, some c165, some c73, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1734 : lratChecker f1734 p1734 = .success := by decide +kernel
theorem unsat1734 : Unsatisfiable (PosFin 57) f1734 := by
  apply lratCheckerSound f1734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1734
  · intro a ha; simp [p1734] at ha; subst a; trivial
  · exact checked1734
theorem derived1734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1734 := by
  apply localUnsat_implies_entails f1734 [c1632, c1710, c1686, c1732, c204, c12, c105, c111, c2, c1733, c1147, c1216, c1219, c27, c1100, c163, c1227, c218, c1709, c348, c165, c73] c1734 unsat1734 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1710 := derived1710 a h
  have h2 : Entails.eval a c1686 := derived1686 a h
  have h3 : Entails.eval a c1732 := derived1732 a h
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c1733 := derived1733 a h
  have h10 : Entails.eval a c1147 := derived1147 a h
  have h11 : Entails.eval a c1216 := derived1216 a h
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c1227 := derived1227 a h
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c1709 := derived1709 a h
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1735 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1734, some c1632, some c1710, some c1686, some c1732, some c204, some c12, some c105, some c111, some c2, some c266, some c265, some c1024, some c4, some c24, some c261, some c161, some c1192, some c885, some c131, some c223, some c211, some c1376, some c168, some c276, some c69, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1735 : lratChecker f1735 p1735 = .success := by decide +kernel
theorem unsat1735 : Unsatisfiable (PosFin 57) f1735 := by
  apply lratCheckerSound f1735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1735
  · intro a ha; simp [p1735] at ha; subst a; trivial
  · exact checked1735
theorem derived1735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1735 := by
  apply localUnsat_implies_entails f1735 [c1734, c1632, c1710, c1686, c1732, c204, c12, c105, c111, c2, c266, c265, c1024, c4, c24, c261, c161, c1192, c885, c131, c223, c211, c1376, c168, c276, c69] c1735 unsat1735 (by rfl) a
  have h0 : Entails.eval a c1734 := derived1734 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1710 := derived1710 a h
  have h3 : Entails.eval a c1686 := derived1686 a h
  have h4 : Entails.eval a c1732 := derived1732 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c1024 := derived1024 a h
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c1192 := derived1192 a h
  have h18 : Entails.eval a c885 := derived885 a h
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c223 := h 222 (by decide)
  have h21 : Entails.eval a c211 := h 210 (by decide)
  have h22 : Entails.eval a c1376 := derived1376 a h
  have h23 : Entails.eval a c168 := h 167 (by decide)
  have h24 : Entails.eval a c276 := h 275 (by decide)
  have h25 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1736 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1686, some c1632, some c1710, some c2, some c1732, some c204, some c12, some c111, some c105, some c1734, some c1735, some c1147, some c1216, some c1219, some c1100, some c1024, some c1717, some c8, some c1709, some c1119, some c165, some c58, some c73, some c351, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1736 : lratChecker f1736 p1736 = .success := by decide +kernel
theorem unsat1736 : Unsatisfiable (PosFin 57) f1736 := by
  apply lratCheckerSound f1736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1736
  · intro a ha; simp [p1736] at ha; subst a; trivial
  · exact checked1736
theorem derived1736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1736 := by
  apply localUnsat_implies_entails f1736 [c1686, c1632, c1710, c2, c1732, c204, c12, c111, c105, c1734, c1735, c1147, c1216, c1219, c1100, c1024, c1717, c8, c1709, c1119, c165, c58, c73, c351] c1736 unsat1736 (by rfl) a
  have h0 : Entails.eval a c1686 := derived1686 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1710 := derived1710 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1732 := derived1732 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c1734 := derived1734 a h
  have h10 : Entails.eval a c1735 := derived1735 a h
  have h11 : Entails.eval a c1147 := derived1147 a h
  have h12 : Entails.eval a c1216 := derived1216 a h
  have h13 : Entails.eval a c1219 := derived1219 a h
  have h14 : Entails.eval a c1100 := derived1100 a h
  have h15 : Entails.eval a c1024 := derived1024 a h
  have h16 : Entails.eval a c1717 := derived1717 a h
  have h17 : Entails.eval a c8 := h 7 (by decide)
  have h18 : Entails.eval a c1709 := derived1709 a h
  have h19 : Entails.eval a c1119 := derived1119 a h
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  have h22 : Entails.eval a c73 := h 72 (by decide)
  have h23 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1737 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1736, some c3, some c1686, some c23, some c163, some c1632, some c157, some c69, some c107, some c35, some c1669, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1737 : lratChecker f1737 p1737 = .success := by decide +kernel
theorem unsat1737 : Unsatisfiable (PosFin 57) f1737 := by
  apply lratCheckerSound f1737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1737
  · intro a ha; simp [p1737] at ha; subst a; trivial
  · exact checked1737
theorem derived1737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1737 := by
  apply localUnsat_implies_entails f1737 [c1736, c3, c1686, c23, c163, c1632, c157, c69, c107, c35, c1669] c1737 unsat1737 (by rfl) a
  have h0 : Entails.eval a c1736 := derived1736 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c1686 := derived1686 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c1669 := derived1669 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1738 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1686, some c1736, some c3, some c23, some c204, some c163, some c1737, some c2, some c12, some c105, some c1573, some c27, some c69, some c106, some c1203, some c349, some c76, some c266, some c265, some c225, some c351, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1738 : lratChecker f1738 p1738 = .success := by decide +kernel
theorem unsat1738 : Unsatisfiable (PosFin 57) f1738 := by
  apply lratCheckerSound f1738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1738
  · intro a ha; simp [p1738] at ha; subst a; trivial
  · exact checked1738
theorem derived1738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1738 := by
  apply localUnsat_implies_entails f1738 [c1632, c1686, c1736, c3, c23, c204, c163, c1737, c2, c12, c105, c1573, c27, c69, c106, c1203, c349, c76, c266, c265, c225, c351] c1738 unsat1738 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1686 := derived1686 a h
  have h2 : Entails.eval a c1736 := derived1736 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c163 := h 162 (by decide)
  have h7 : Entails.eval a c1737 := derived1737 a h
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c1573 := derived1573 a h
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c1203 := derived1203 a h
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c76 := h 75 (by decide)
  have h18 : Entails.eval a c266 := h 265 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c225 := h 224 (by decide)
  have h21 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1739 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c1738, some c1632, some c1332, some c16, some c106, some c201, some c1346, some c1469, some c22, some c982, some c158, some c1634, some c243, some c73, some c72, some c175, some c140, some c239, some c284, some c139, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1739 : lratChecker f1739 p1739 = .success := by decide +kernel
theorem unsat1739 : Unsatisfiable (PosFin 57) f1739 := by
  apply lratCheckerSound f1739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1739
  · intro a ha; simp [p1739] at ha; subst a; trivial
  · exact checked1739
theorem derived1739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1739 := by
  apply localUnsat_implies_entails f1739 [c7, c1738, c1632, c1332, c16, c106, c201, c1346, c1469, c22, c982, c158, c1634, c243, c73, c72, c175, c140, c239, c284, c139] c1739 unsat1739 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1332 := derived1332 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c1346 := derived1346 a h
  have h8 : Entails.eval a c1469 := derived1469 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c982 := derived982 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c1634 := derived1634 a h
  have h13 : Entails.eval a c243 := h 242 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1740 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c7, some c268, some c1632, some c1739, some c111, some c32, some c266, some c1348, some c39, some c20, some c106, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1740 : lratChecker f1740 p1740 = .success := by decide +kernel
theorem unsat1740 : Unsatisfiable (PosFin 57) f1740 := by
  apply lratCheckerSound f1740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1740
  · intro a ha; simp [p1740] at ha; subst a; trivial
  · exact checked1740
theorem derived1740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1740 := by
  apply localUnsat_implies_entails f1740 [c1738, c7, c268, c1632, c1739, c111, c32, c266, c1348, c39, c20, c106] c1740 unsat1740 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c1739 := derived1739 a h
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1348 := derived1348 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1741 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c7, some c268, some c1740, some c1147, some c201, some c16, some c111, some c5, some c32, some c25, some c264, some c1348, some c116, some c263, some c446, some c123, some c280, some c153, some c219, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1741 : lratChecker f1741 p1741 = .success := by decide +kernel
theorem unsat1741 : Unsatisfiable (PosFin 57) f1741 := by
  apply lratCheckerSound f1741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1741
  · intro a ha; simp [p1741] at ha; subst a; trivial
  · exact checked1741
theorem derived1741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1741 := by
  apply localUnsat_implies_entails f1741 [c1738, c1632, c7, c268, c1740, c1147, c201, c16, c111, c5, c32, c25, c264, c1348, c116, c263, c446, c123, c280, c153, c219] c1741 unsat1741 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1740 := derived1740 a h
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c1348 := derived1348 a h
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c446 := derived446 a h
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c153 := h 152 (by decide)
  have h20 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1742 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c105, some c1738, some c1632, some c266, some c262, some c32, some c268, some c267, some c119, some c128, some c43, some c51, some c201, some c205, some c207, some c146, some c316, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1742 : lratChecker f1742 p1742 = .success := by decide +kernel
theorem unsat1742 : Unsatisfiable (PosFin 57) f1742 := by
  apply lratCheckerSound f1742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1742
  · intro a ha; simp [p1742] at ha; subst a; trivial
  · exact checked1742
theorem derived1742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1742 := by
  apply localUnsat_implies_entails f1742 [c1741, c105, c1738, c1632, c266, c262, c32, c268, c267, c119, c128, c43, c51, c201, c205, c207, c146, c316] c1742 unsat1742 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1743 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1741, some c105, some c107, some c1738, some c1632, some c39, some c982, some c8, some c28, some c1460, some c268, some c267, some c58, some c22, some c68, some c188, some c119, some c128, some c249, some c186, some c103, some c43, some c51, some c142, some c135, some c156, some c87, some c85, some c361, some c374, some c335, some c645, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1743 : lratChecker f1743 p1743 = .success := by decide +kernel
theorem unsat1743 : Unsatisfiable (PosFin 57) f1743 := by
  apply lratCheckerSound f1743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1743
  · intro a ha; simp [p1743] at ha; subst a; trivial
  · exact checked1743
theorem derived1743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1743 := by
  apply localUnsat_implies_entails f1743 [c1741, c105, c107, c1738, c1632, c39, c982, c8, c28, c1460, c268, c267, c58, c22, c68, c188, c119, c128, c249, c186, c103, c43, c51, c142, c135, c156, c87, c85, c361, c374, c335, c645] c1743 unsat1743 (by rfl) a
  have h0 : Entails.eval a c1741 := derived1741 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c982 := derived982 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c1460 := derived1460 a h
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  have h18 : Entails.eval a c249 := h 248 (by decide)
  have h19 : Entails.eval a c186 := h 185 (by decide)
  have h20 : Entails.eval a c103 := h 102 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c142 := h 141 (by decide)
  have h24 : Entails.eval a c135 := h 134 (by decide)
  have h25 : Entails.eval a c156 := h 155 (by decide)
  have h26 : Entails.eval a c87 := h 86 (by decide)
  have h27 : Entails.eval a c85 := h 84 (by decide)
  have h28 : Entails.eval a c361 := h 360 (by decide)
  have h29 : Entails.eval a c374 := h 373 (by decide)
  have h30 : Entails.eval a c335 := h 334 (by decide)
  have h31 : Entails.eval a c645 := derived645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1744 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c267, some c128, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1744 : lratChecker f1744 p1744 = .success := by decide +kernel
theorem unsat1744 : Unsatisfiable (PosFin 57) f1744 := by
  apply lratCheckerSound f1744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1744
  · intro a ha; simp [p1744] at ha; subst a; trivial
  · exact checked1744
theorem derived1744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1744 := by
  apply localUnsat_implies_entails f1744 [c268, c267, c128] c1744 unsat1744 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1745 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1741, some c107, some c105, some c1743, some c1742, some c1147, some c202, some c201, some c1275, some c19, some c1744, some c32, some c25, some c264, some c128, some c116, some c1723, some c446, some c123, some c280, some c153, some c219, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1745 : lratChecker f1745 p1745 = .success := by decide +kernel
theorem unsat1745 : Unsatisfiable (PosFin 57) f1745 := by
  apply lratCheckerSound f1745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1745
  · intro a ha; simp [p1745] at ha; subst a; trivial
  · exact checked1745
theorem derived1745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1745 := by
  apply localUnsat_implies_entails f1745 [c1738, c1632, c1741, c107, c105, c1743, c1742, c1147, c202, c201, c1275, c19, c1744, c32, c25, c264, c128, c116, c1723, c446, c123, c280, c153, c219] c1745 unsat1745 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1741 := derived1741 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1743 := derived1743 a h
  have h6 : Entails.eval a c1742 := derived1742 a h
  have h7 : Entails.eval a c1147 := derived1147 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c1275 := derived1275 a h
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c1744 := derived1744 a h
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c264 := h 263 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c1723 := derived1723 a h
  have h19 : Entails.eval a c446 := derived446 a h
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c280 := h 279 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  have h23 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1746 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c33, some c111, some c22, some c1083, some c1597, some c1296, some c1745, some c1275, some c1634, some c17, some c158, some c73, some c72, some c60, some c351, some c186, some c257, some c97, some c339, some c353, some c343, some c194, some c1192, some c117, some c146, some c147, some c41, some c317, some c205, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1746 : lratChecker f1746 p1746 = .success := by decide +kernel
theorem unsat1746 : Unsatisfiable (PosFin 57) f1746 := by
  apply lratCheckerSound f1746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1746
  · intro a ha; simp [p1746] at ha; subst a; trivial
  · exact checked1746
theorem derived1746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1746 := by
  apply localUnsat_implies_entails f1746 [c1738, c1632, c33, c111, c22, c1083, c1597, c1296, c1745, c1275, c1634, c17, c158, c73, c72, c60, c351, c186, c257, c97, c339, c353, c343, c194, c1192, c117, c146, c147, c41, c317, c205] c1746 unsat1746 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1083 := derived1083 a h
  have h6 : Entails.eval a c1597 := derived1597 a h
  have h7 : Entails.eval a c1296 := derived1296 a h
  have h8 : Entails.eval a c1745 := derived1745 a h
  have h9 : Entails.eval a c1275 := derived1275 a h
  have h10 : Entails.eval a c1634 := derived1634 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c351 := h 350 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c97 := h 96 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c353 := h 352 (by decide)
  have h22 : Entails.eval a c343 := h 342 (by decide)
  have h23 : Entails.eval a c194 := h 193 (by decide)
  have h24 : Entails.eval a c1192 := derived1192 a h
  have h25 : Entails.eval a c117 := h 116 (by decide)
  have h26 : Entails.eval a c146 := h 145 (by decide)
  have h27 : Entails.eval a c147 := h 146 (by decide)
  have h28 : Entails.eval a c41 := h 40 (by decide)
  have h29 : Entails.eval a c317 := h 316 (by decide)
  have h30 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1747 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c138, some c146, some c243, some c241, some c315, some c293, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1747 : lratChecker f1747 p1747 = .success := by decide +kernel
theorem unsat1747 : Unsatisfiable (PosFin 57) f1747 := by
  apply lratCheckerSound f1747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1747
  · intro a ha; simp [p1747] at ha; subst a; trivial
  · exact checked1747
theorem derived1747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1747 := by
  apply localUnsat_implies_entails f1747 [c138, c146, c243, c241, c315, c293] c1747 unsat1747 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1748 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c1746, some c106, some c111, some c1632, some c22, some c1083, some c1738, some c1296, some c1745, some c199, some c202, some c1316, some c113, some c1342, some c117, some c44, some c1747, some c1343, some c316, some c136, some c237, some c241, some c174, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1748 : lratChecker f1748 p1748 = .success := by decide +kernel
theorem unsat1748 : Unsatisfiable (PosFin 57) f1748 := by
  apply lratCheckerSound f1748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1748
  · intro a ha; simp [p1748] at ha; subst a; trivial
  · exact checked1748
theorem derived1748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1748 := by
  apply localUnsat_implies_entails f1748 [c262, c1746, c106, c111, c1632, c22, c1083, c1738, c1296, c1745, c199, c202, c1316, c113, c1342, c117, c44, c1747, c1343, c316, c136, c237, c241, c174] c1748 unsat1748 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c1746 := derived1746 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1083 := derived1083 a h
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c1296 := derived1296 a h
  have h9 : Entails.eval a c1745 := derived1745 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c1316 := derived1316 a h
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c1342 := derived1342 a h
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c1747 := derived1747 a h
  have h18 : Entails.eval a c1343 := derived1343 a h
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c136 := h 135 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c241 := h 240 (by decide)
  have h23 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1749 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1748, some c262, some c1746, some c106, some c111, some c1632, some c22, some c1083, some c1738, some c1296, some c1745, some c197, some c1316, some c113, some c1342, some c44, some c147, some c1747, some c315, some c1343, some c149, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1749 : lratChecker f1749 p1749 = .success := by decide +kernel
theorem unsat1749 : Unsatisfiable (PosFin 57) f1749 := by
  apply lratCheckerSound f1749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1749
  · intro a ha; simp [p1749] at ha; subst a; trivial
  · exact checked1749
theorem derived1749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1749 := by
  apply localUnsat_implies_entails f1749 [c1748, c262, c1746, c106, c111, c1632, c22, c1083, c1738, c1296, c1745, c197, c1316, c113, c1342, c44, c147, c1747, c315, c1343, c149] c1749 unsat1749 (by rfl) a
  have h0 : Entails.eval a c1748 := derived1748 a h
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c1746 := derived1746 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c1083 := derived1083 a h
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c1296 := derived1296 a h
  have h10 : Entails.eval a c1745 := derived1745 a h
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c1316 := derived1316 a h
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c1342 := derived1342 a h
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c1747 := derived1747 a h
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c1343 := derived1343 a h
  have h20 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1750 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1748, some c262, some c1738, some c1296, some c1749, some c1192, some c117, some c146, some c147, some c41, some c317, some c205, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1750 : lratChecker f1750 p1750 = .success := by decide +kernel
theorem unsat1750 : Unsatisfiable (PosFin 57) f1750 := by
  apply lratCheckerSound f1750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1750
  · intro a ha; simp [p1750] at ha; subst a; trivial
  · exact checked1750
theorem derived1750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1750 := by
  apply localUnsat_implies_entails f1750 [c1748, c262, c1738, c1296, c1749, c1192, c117, c146, c147, c41, c317, c205] c1750 unsat1750 (by rfl) a
  have h0 : Entails.eval a c1748 := derived1748 a h
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1296 := derived1296 a h
  have h4 : Entails.eval a c1749 := derived1749 a h
  have h5 : Entails.eval a c1192 := derived1192 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1751 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c33, some c111, some c22, some c1083, some c1597, some c1745, some c262, some c1746, some c106, some c1748, some c1750, some c201, some c159, some c62, some c76, some c187, some c259, some c257, some c60, some c349, some c340, some c348, some c457, some c182, some c1316, some c113, some c1342, some c44, some c274, some c149, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1751 : lratChecker f1751 p1751 = .success := by decide +kernel
theorem unsat1751 : Unsatisfiable (PosFin 57) f1751 := by
  apply lratCheckerSound f1751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1751
  · intro a ha; simp [p1751] at ha; subst a; trivial
  · exact checked1751
theorem derived1751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1751 := by
  apply localUnsat_implies_entails f1751 [c1738, c1632, c33, c111, c22, c1083, c1597, c1745, c262, c1746, c106, c1748, c1750, c201, c159, c62, c76, c187, c259, c257, c60, c349, c340, c348, c457, c182, c1316, c113, c1342, c44, c274, c149] c1751 unsat1751 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1083 := derived1083 a h
  have h6 : Entails.eval a c1597 := derived1597 a h
  have h7 : Entails.eval a c1745 := derived1745 a h
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c1746 := derived1746 a h
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c1748 := derived1748 a h
  have h12 : Entails.eval a c1750 := derived1750 a h
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c187 := h 186 (by decide)
  have h18 : Entails.eval a c259 := h 258 (by decide)
  have h19 : Entails.eval a c257 := h 256 (by decide)
  have h20 : Entails.eval a c60 := h 59 (by decide)
  have h21 : Entails.eval a c349 := h 348 (by decide)
  have h22 : Entails.eval a c340 := h 339 (by decide)
  have h23 : Entails.eval a c348 := h 347 (by decide)
  have h24 : Entails.eval a c457 := derived457 a h
  have h25 : Entails.eval a c182 := h 181 (by decide)
  have h26 : Entails.eval a c1316 := derived1316 a h
  have h27 : Entails.eval a c113 := h 112 (by decide)
  have h28 : Entails.eval a c1342 := derived1342 a h
  have h29 : Entails.eval a c44 := h 43 (by decide)
  have h30 : Entails.eval a c274 := h 273 (by decide)
  have h31 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1752 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1296, some c1745, some c1632, some c22, some c1751, some c1334, some c982, some c1316, some c106, some c1342, some c215, some c44, some c317, some c113, some c133, some c77, some c230, some c294, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1752 : lratChecker f1752 p1752 = .success := by decide +kernel
theorem unsat1752 : Unsatisfiable (PosFin 57) f1752 := by
  apply lratCheckerSound f1752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1752
  · intro a ha; simp [p1752] at ha; subst a; trivial
  · exact checked1752
theorem derived1752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1752 := by
  apply localUnsat_implies_entails f1752 [c1738, c1296, c1745, c1632, c22, c1751, c1334, c982, c1316, c106, c1342, c215, c44, c317, c113, c133, c77, c230, c294] c1752 unsat1752 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1296 := derived1296 a h
  have h2 : Entails.eval a c1745 := derived1745 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c1751 := derived1751 a h
  have h6 : Entails.eval a c1334 := derived1334 a h
  have h7 : Entails.eval a c982 := derived982 a h
  have h8 : Entails.eval a c1316 := derived1316 a h
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c1342 := derived1342 a h
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c317 := h 316 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c230 := h 229 (by decide)
  have h18 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1753 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1745, some c1738, some c1632, some c111, some c1296, some c1752, some c264, some c266, some c1346, some c1024, some c4, some c1083, some c24, some c1334, some c106, some c58, some c69, some c1316, some c1345, some c251, some c215, some c117, some c62, some c44, some c164, some c142, some c227, some c1695, some c284, some c283, some c511, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1753 : lratChecker f1753 p1753 = .success := by decide +kernel
theorem unsat1753 : Unsatisfiable (PosFin 57) f1753 := by
  apply lratCheckerSound f1753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1753
  · intro a ha; simp [p1753] at ha; subst a; trivial
  · exact checked1753
theorem derived1753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1753 := by
  apply localUnsat_implies_entails f1753 [c1745, c1738, c1632, c111, c1296, c1752, c264, c266, c1346, c1024, c4, c1083, c24, c1334, c106, c58, c69, c1316, c1345, c251, c215, c117, c62, c44, c164, c142, c227, c1695, c284, c283, c511] c1753 unsat1753 (by rfl) a
  have h0 : Entails.eval a c1745 := derived1745 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1296 := derived1296 a h
  have h5 : Entails.eval a c1752 := derived1752 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1346 := derived1346 a h
  have h9 : Entails.eval a c1024 := derived1024 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c1083 := derived1083 a h
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c1334 := derived1334 a h
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c1316 := derived1316 a h
  have h18 : Entails.eval a c1345 := derived1345 a h
  have h19 : Entails.eval a c251 := h 250 (by decide)
  have h20 : Entails.eval a c215 := h 214 (by decide)
  have h21 : Entails.eval a c117 := h 116 (by decide)
  have h22 : Entails.eval a c62 := h 61 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  have h24 : Entails.eval a c164 := h 163 (by decide)
  have h25 : Entails.eval a c142 := h 141 (by decide)
  have h26 : Entails.eval a c227 := h 226 (by decide)
  have h27 : Entails.eval a c1695 := derived1695 a h
  have h28 : Entails.eval a c284 := h 283 (by decide)
  have h29 : Entails.eval a c283 := h 282 (by decide)
  have h30 : Entails.eval a c511 := derived511 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1754 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c32, some c33, some c268, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1754 : lratChecker f1754 p1754 = .success := by decide +kernel
theorem unsat1754 : Unsatisfiable (PosFin 57) f1754 := by
  apply lratCheckerSound f1754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1754
  · intro a ha; simp [p1754] at ha; subst a; trivial
  · exact checked1754
theorem derived1754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1754 := by
  apply localUnsat_implies_entails f1754 [c1738, c1632, c32, c33, c268] c1754 unsat1754 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1755 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c982, some c8, some c28, some c69, some c168, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1755 : lratChecker f1755 p1755 = .success := by decide +kernel
theorem unsat1755 : Unsatisfiable (PosFin 57) f1755 := by
  apply lratCheckerSound f1755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1755
  · intro a ha; simp [p1755] at ha; subst a; trivial
  · exact checked1755
theorem derived1755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1755 := by
  apply localUnsat_implies_entails f1755 [c982, c8, c28, c69, c168] c1755 unsat1755 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1756 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c197, some c1632, some c1755, some c106, some c1738, some c1754, some c264, some c123, some c113, some c44, some c120, some c1696, some c168, some c166, some c225, some c68, some c158, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1756 : lratChecker f1756 p1756 = .success := by decide +kernel
theorem unsat1756 : Unsatisfiable (PosFin 57) f1756 := by
  apply lratCheckerSound f1756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1756
  · intro a ha; simp [p1756] at ha; subst a; trivial
  · exact checked1756
theorem derived1756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1756 := by
  apply localUnsat_implies_entails f1756 [c197, c1632, c1755, c106, c1738, c1754, c264, c123, c113, c44, c120, c1696, c168, c166, c225, c68, c158] c1756 unsat1756 (by rfl) a
  have h0 : Entails.eval a c197 := h 196 (by decide)
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1755 := derived1755 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1738 := derived1738 a h
  have h5 : Entails.eval a c1754 := derived1754 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c1696 := derived1696 a h
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c166 := h 165 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1757 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1696, some c168, some c166, some c225, some c68, some c74, some c350, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1757 : lratChecker f1757 p1757 = .success := by decide +kernel
theorem unsat1757 : Unsatisfiable (PosFin 57) f1757 := by
  apply lratCheckerSound f1757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1757
  · intro a ha; simp [p1757] at ha; subst a; trivial
  · exact checked1757
theorem derived1757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1757 := by
  apply localUnsat_implies_entails f1757 [c1696, c168, c166, c225, c68, c74, c350] c1757 unsat1757 (by rfl) a
  have h0 : Entails.eval a c1696 := derived1696 a h
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1758 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1745, some c1738, some c1632, some c1753, some c1754, some c264, some c266, some c1348, some c1417, some c1755, some c106, some c18, some c197, some c1756, some c1757, some c1498, some c120, some c44, some c142, some c133, some c49, some c230, some c1700, some c893, some c85, some c212, some c887, some c268, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1758 : lratChecker f1758 p1758 = .success := by decide +kernel
theorem unsat1758 : Unsatisfiable (PosFin 57) f1758 := by
  apply lratCheckerSound f1758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1758
  · intro a ha; simp [p1758] at ha; subst a; trivial
  · exact checked1758
theorem derived1758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1758 := by
  apply localUnsat_implies_entails f1758 [c1745, c1738, c1632, c1753, c1754, c264, c266, c1348, c1417, c1755, c106, c18, c197, c1756, c1757, c1498, c120, c44, c142, c133, c49, c230, c1700, c893, c85, c212, c887, c268] c1758 unsat1758 (by rfl) a
  have h0 : Entails.eval a c1745 := derived1745 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1753 := derived1753 a h
  have h4 : Entails.eval a c1754 := derived1754 a h
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c1348 := derived1348 a h
  have h8 : Entails.eval a c1417 := derived1417 a h
  have h9 : Entails.eval a c1755 := derived1755 a h
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c1756 := derived1756 a h
  have h14 : Entails.eval a c1757 := derived1757 a h
  have h15 : Entails.eval a c1498 := derived1498 a h
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c142 := h 141 (by decide)
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c49 := h 48 (by decide)
  have h21 : Entails.eval a c230 := h 229 (by decide)
  have h22 : Entails.eval a c1700 := derived1700 a h
  have h23 : Entails.eval a c893 := derived893 a h
  have h24 : Entails.eval a c85 := h 84 (by decide)
  have h25 : Entails.eval a c212 := h 211 (by decide)
  have h26 : Entails.eval a c887 := derived887 a h
  have h27 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1759 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1738, some c1632, some c1613, some c1275, some c264, some c106, some c22, some c1678, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1759 : lratChecker f1759 p1759 = .success := by decide +kernel
theorem unsat1759 : Unsatisfiable (PosFin 57) f1759 := by
  apply lratCheckerSound f1759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1759
  · intro a ha; simp [p1759] at ha; subst a; trivial
  · exact checked1759
theorem derived1759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1759 := by
  apply localUnsat_implies_entails f1759 [c1147, c1738, c1632, c1613, c1275, c264, c106, c22, c1678] c1759 unsat1759 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1613 := derived1613 a h
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1678 := derived1678 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1760 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨48, by decide⟩, false), (⟨44, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c171, some c232, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1760 : lratChecker f1760 p1760 = .success := by decide +kernel
theorem unsat1760 : Unsatisfiable (PosFin 57) f1760 := by
  apply lratCheckerSound f1760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1760
  · intro a ha; simp [p1760] at ha; subst a; trivial
  · exact checked1760
theorem derived1760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1760 := by
  apply localUnsat_implies_entails f1760 [c123, c171, c232] c1760 unsat1760 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1761 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1745, some c1738, some c1758, some c1147, some c202, some c201, some c1759, some c111, some c1754, some c264, some c1348, some c116, some c49, some c135, some c85, some c177, some c1760, some c197, some c1225, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1761 : lratChecker f1761 p1761 = .success := by decide +kernel
theorem unsat1761 : Unsatisfiable (PosFin 57) f1761 := by
  apply lratCheckerSound f1761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1761
  · intro a ha; simp [p1761] at ha; subst a; trivial
  · exact checked1761
theorem derived1761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1761 := by
  apply localUnsat_implies_entails f1761 [c1745, c1738, c1758, c1147, c202, c201, c1759, c111, c1754, c264, c1348, c116, c49, c135, c85, c177, c1760, c197, c1225] c1761 unsat1761 (by rfl) a
  have h0 : Entails.eval a c1745 := derived1745 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1758 := derived1758 a h
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c1759 := derived1759 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c1754 := derived1754 a h
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c1348 := derived1348 a h
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c135 := h 134 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c1760 := derived1760 a h
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c1225 := derived1225 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1762 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c849, some c201, some c209, some c212, some c316, some c49, some c146, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1762 : lratChecker f1762 p1762 = .success := by decide +kernel
theorem unsat1762 : Unsatisfiable (PosFin 57) f1762 := by
  apply lratCheckerSound f1762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1762
  · intro a ha; simp [p1762] at ha; subst a; trivial
  · exact checked1762
theorem derived1762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1762 := by
  apply localUnsat_implies_entails f1762 [c123, c849, c201, c209, c212, c316, c49, c146] c1762 unsat1762 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c849 := derived849 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1763 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1761, some c105, some c1745, some c107, some c1137, some c1738, some c1632, some c22, some c32, some c982, some c268, some c267, some c1083, some c1762, some c262, some c1147, some c1678, some c202, some c201, some c159, some c19, some c116, some c228, some c166, some c49, some c53, some c75, some c147, some c216, some c284, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1763 : lratChecker f1763 p1763 = .success := by decide +kernel
theorem unsat1763 : Unsatisfiable (PosFin 57) f1763 := by
  apply lratCheckerSound f1763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1763
  · intro a ha; simp [p1763] at ha; subst a; trivial
  · exact checked1763
theorem derived1763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1763 := by
  apply localUnsat_implies_entails f1763 [c1761, c105, c1745, c107, c1137, c1738, c1632, c22, c32, c982, c268, c267, c1083, c1762, c262, c1147, c1678, c202, c201, c159, c19, c116, c228, c166, c49, c53, c75, c147, c216, c284] c1763 unsat1763 (by rfl) a
  have h0 : Entails.eval a c1761 := derived1761 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1745 := derived1745 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1137 := derived1137 a h
  have h5 : Entails.eval a c1738 := derived1738 a h
  have h6 : Entails.eval a c1632 := derived1632 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c982 := derived982 a h
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c1083 := derived1083 a h
  have h13 : Entails.eval a c1762 := derived1762 a h
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c1147 := derived1147 a h
  have h16 : Entails.eval a c1678 := derived1678 a h
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c201 := h 200 (by decide)
  have h19 : Entails.eval a c159 := h 158 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  have h23 : Entails.eval a c166 := h 165 (by decide)
  have h24 : Entails.eval a c49 := h 48 (by decide)
  have h25 : Entails.eval a c53 := h 52 (by decide)
  have h26 : Entails.eval a c75 := h 74 (by decide)
  have h27 : Entails.eval a c147 := h 146 (by decide)
  have h28 : Entails.eval a c216 := h 215 (by decide)
  have h29 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1764 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨18, by decide⟩, false), (⟨47, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c264, some c1137, some c1632, some c266, some c8, some c39, some c982, some c28, some c268, some c58, some c68, some c168, some c249, some c251, some c188, some c224, some c103, some c352, some c339, some c347, some c335, some c374, some c245, some c365, some c123, some c331, some c186, some c361, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1764 : lratChecker f1764 p1764 = .success := by decide +kernel
theorem unsat1764 : Unsatisfiable (PosFin 57) f1764 := by
  apply lratCheckerSound f1764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1764
  · intro a ha; simp [p1764] at ha; subst a; trivial
  · exact checked1764
theorem derived1764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1764 := by
  apply localUnsat_implies_entails f1764 [c1738, c264, c1137, c1632, c266, c8, c39, c982, c28, c268, c58, c68, c168, c249, c251, c188, c224, c103, c352, c339, c347, c335, c374, c245, c365, c123, c331, c186, c361] c1764 unsat1764 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c1137 := derived1137 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c982 := derived982 a h
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c339 := h 338 (by decide)
  have h20 : Entails.eval a c347 := h 346 (by decide)
  have h21 : Entails.eval a c335 := h 334 (by decide)
  have h22 : Entails.eval a c374 := h 373 (by decide)
  have h23 : Entails.eval a c245 := h 244 (by decide)
  have h24 : Entails.eval a c365 := h 364 (by decide)
  have h25 : Entails.eval a c123 := h 122 (by decide)
  have h26 : Entails.eval a c331 := h 330 (by decide)
  have h27 : Entails.eval a c186 := h 185 (by decide)
  have h28 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1765 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1745, some c1761, some c107, some c105, some c1137, some c1427, some c1763, some c264, some c1346, some c1764, some c1147, some c202, some c201, some c1348, some c116, some c49, some c135, some c85, some c177, some c1760, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1765 : lratChecker f1765 p1765 = .success := by decide +kernel
theorem unsat1765 : Unsatisfiable (PosFin 57) f1765 := by
  apply lratCheckerSound f1765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1765
  · intro a ha; simp [p1765] at ha; subst a; trivial
  · exact checked1765
theorem derived1765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1765 := by
  apply localUnsat_implies_entails f1765 [c1738, c1745, c1761, c107, c105, c1137, c1427, c1763, c264, c1346, c1764, c1147, c202, c201, c1348, c116, c49, c135, c85, c177, c1760] c1765 unsat1765 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1745 := derived1745 a h
  have h2 : Entails.eval a c1761 := derived1761 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1427 := derived1427 a h
  have h7 : Entails.eval a c1763 := derived1763 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1346 := derived1346 a h
  have h10 : Entails.eval a c1764 := derived1764 a h
  have h11 : Entails.eval a c1147 := derived1147 a h
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c1348 := derived1348 a h
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c135 := h 134 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c177 := h 176 (by decide)
  have h20 : Entails.eval a c1760 := derived1760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1766 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1765, some c1632, some c13, some c1738, some c2, some c264, some c111, some c1296, some c1613, some c1299, some c266, some c1334, some c1316, some c215, some c44, some c113, some c142, some c1711, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1766 : lratChecker f1766 p1766 = .success := by decide +kernel
theorem unsat1766 : Unsatisfiable (PosFin 57) f1766 := by
  apply lratCheckerSound f1766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1766
  · intro a ha; simp [p1766] at ha; subst a; trivial
  · exact checked1766
theorem derived1766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1766 := by
  apply localUnsat_implies_entails f1766 [c1765, c1632, c13, c1738, c2, c264, c111, c1296, c1613, c1299, c266, c1334, c1316, c215, c44, c113, c142, c1711] c1766 unsat1766 (by rfl) a
  have h0 : Entails.eval a c1765 := derived1765 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1296 := derived1296 a h
  have h8 : Entails.eval a c1613 := derived1613 a h
  have h9 : Entails.eval a c1299 := derived1299 a h
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c1334 := derived1334 a h
  have h12 : Entails.eval a c1316 := derived1316 a h
  have h13 : Entails.eval a c215 := h 214 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c1711 := derived1711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1767 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c39, some c28, some c268, some c168, some c27, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1767 : lratChecker f1767 p1767 = .success := by decide +kernel
theorem unsat1767 : Unsatisfiable (PosFin 57) f1767 := by
  apply lratCheckerSound f1767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1767
  · intro a ha; simp [p1767] at ha; subst a; trivial
  · exact checked1767
theorem derived1767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1767 := by
  apply localUnsat_implies_entails f1767 [c8, c39, c28, c268, c168, c27] c1767 unsat1767 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1768 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c27, some c539, some c168, some c68, some c74, some c225, some c350, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1768 : lratChecker f1768 p1768 = .success := by decide +kernel
theorem unsat1768 : Unsatisfiable (PosFin 57) f1768 := by
  apply lratCheckerSound f1768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1768
  · intro a ha; simp [p1768] at ha; subst a; trivial
  · exact checked1768
theorem derived1768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1768 := by
  apply localUnsat_implies_entails f1768 [c27, c539, c168, c68, c74, c225, c350] c1768 unsat1768 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1769 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c76, some c350, some c351, some c225, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1769 : lratChecker f1769 p1769 = .success := by decide +kernel
theorem unsat1769 : Unsatisfiable (PosFin 57) f1769 := by
  apply lratCheckerSound f1769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1769
  · intro a ha; simp [p1769] at ha; subst a; trivial
  · exact checked1769
theorem derived1769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1769 := by
  apply localUnsat_implies_entails f1769 [c69, c76, c350, c351, c225] c1769 unsat1769 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c350 := h 349 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1770 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1767, some c106, some c1769, some c166, some c68, some c74, some c350, some c351, some c225, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1770 : lratChecker f1770 p1770 = .success := by decide +kernel
theorem unsat1770 : Unsatisfiable (PosFin 57) f1770 := by
  apply lratCheckerSound f1770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1770
  · intro a ha; simp [p1770] at ha; subst a; trivial
  · exact checked1770
theorem derived1770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1770 := by
  apply localUnsat_implies_entails f1770 [c1738, c1632, c1767, c106, c1769, c166, c68, c74, c350, c351, c225] c1770 unsat1770 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1767 := derived1767 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1769 := derived1769 a h
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c351 := h 350 (by decide)
  have h10 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1771 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c27, some c539, some c168, some c75, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1771 : lratChecker f1771 p1771 = .success := by decide +kernel
theorem unsat1771 : Unsatisfiable (PosFin 57) f1771 := by
  apply lratCheckerSound f1771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1771
  · intro a ha; simp [p1771] at ha; subst a; trivial
  · exact checked1771
theorem derived1771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1771 := by
  apply localUnsat_implies_entails f1771 [c27, c539, c168, c75] c1771 unsat1771 (by rfl) a
  have h0 : Entails.eval a c27 := h 26 (by decide)
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1772 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c264, some c1770, some c266, some c1147, some c197, some c1632, some c1227, some c26, some c1771, some c268, some c1723, some c25, some c123, some c113, some c1614, some c42, some c219, some c214, some c269, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1772 : lratChecker f1772 p1772 = .success := by decide +kernel
theorem unsat1772 : Unsatisfiable (PosFin 57) f1772 := by
  apply lratCheckerSound f1772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1772
  · intro a ha; simp [p1772] at ha; subst a; trivial
  · exact checked1772
theorem derived1772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1772 := by
  apply localUnsat_implies_entails f1772 [c1738, c264, c1770, c266, c1147, c197, c1632, c1227, c26, c1771, c268, c1723, c25, c123, c113, c1614, c42, c219, c214, c269] c1772 unsat1772 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c1770 := derived1770 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c1632 := derived1632 a h
  have h7 : Entails.eval a c1227 := derived1227 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1771 := derived1771 a h
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c1723 := derived1723 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c1614 := derived1614 a h
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  have h18 : Entails.eval a c214 := h 213 (by decide)
  have h19 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1773 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1765, some c2, some c1738, some c264, some c13, some c1766, some c12, some c1770, some c268, some c539, some c61, some c194, some c97, some c252, some c68, some c75, some c351, some c27, some c348, some c254, some c266, some c40, some c1772, some c1147, some c197, some c1417, some c123, some c113, some c219, some c192, some c42, some c349, some c216, some c339, some c335, some c312, some c314, some c147, some c140, some c49, some c236, some c333, some c169, some c134, some c361, some c78, some c85, some c294, some c403, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1773 : lratChecker f1773 p1773 = .success := by decide +kernel
theorem unsat1773 : Unsatisfiable (PosFin 57) f1773 := by
  apply lratCheckerSound f1773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1773
  · intro a ha; simp [p1773] at ha; subst a; trivial
  · exact checked1773
theorem derived1773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1773 := by
  apply localUnsat_implies_entails f1773 [c1632, c1765, c2, c1738, c264, c13, c1766, c12, c1770, c268, c539, c61, c194, c97, c252, c68, c75, c351, c27, c348, c254, c266, c40, c1772, c1147, c197, c1417, c123, c113, c219, c192, c42, c349, c216, c339, c335, c312, c314, c147, c140, c49, c236, c333, c169, c134, c361, c78, c85, c294, c403] c1773 unsat1773 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1765 := derived1765 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c1766 := derived1766 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c1770 := derived1770 a h
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c539 := derived539 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c351 := h 350 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c254 := h 253 (by decide)
  have h21 : Entails.eval a c266 := h 265 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  have h23 : Entails.eval a c1772 := derived1772 a h
  have h24 : Entails.eval a c1147 := derived1147 a h
  have h25 : Entails.eval a c197 := h 196 (by decide)
  have h26 : Entails.eval a c1417 := derived1417 a h
  have h27 : Entails.eval a c123 := h 122 (by decide)
  have h28 : Entails.eval a c113 := h 112 (by decide)
  have h29 : Entails.eval a c219 := h 218 (by decide)
  have h30 : Entails.eval a c192 := h 191 (by decide)
  have h31 : Entails.eval a c42 := h 41 (by decide)
  have h32 : Entails.eval a c349 := h 348 (by decide)
  have h33 : Entails.eval a c216 := h 215 (by decide)
  have h34 : Entails.eval a c339 := h 338 (by decide)
  have h35 : Entails.eval a c335 := h 334 (by decide)
  have h36 : Entails.eval a c312 := h 311 (by decide)
  have h37 : Entails.eval a c314 := h 313 (by decide)
  have h38 : Entails.eval a c147 := h 146 (by decide)
  have h39 : Entails.eval a c140 := h 139 (by decide)
  have h40 : Entails.eval a c49 := h 48 (by decide)
  have h41 : Entails.eval a c236 := h 235 (by decide)
  have h42 : Entails.eval a c333 := h 332 (by decide)
  have h43 : Entails.eval a c169 := h 168 (by decide)
  have h44 : Entails.eval a c134 := h 133 (by decide)
  have h45 : Entails.eval a c361 := h 360 (by decide)
  have h46 : Entails.eval a c78 := h 77 (by decide)
  have h47 : Entails.eval a c85 := h 84 (by decide)
  have h48 : Entails.eval a c294 := h 293 (by decide)
  have h49 : Entails.eval a c403 := h 402 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1774 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1765, some c2, some c13, some c1766, some c12, some c1772, some c1738, some c264, some c1770, some c197, some c268, some c539, some c68, some c61, some c75, some c254, some c194, some c97, some c252, some c1773, some c1731, some c140, some c360, some c276, some c233, some c134, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1774 : lratChecker f1774 p1774 = .success := by decide +kernel
theorem unsat1774 : Unsatisfiable (PosFin 57) f1774 := by
  apply lratCheckerSound f1774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1774
  · intro a ha; simp [p1774] at ha; subst a; trivial
  · exact checked1774
theorem derived1774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1774 := by
  apply localUnsat_implies_entails f1774 [c1632, c1765, c2, c13, c1766, c12, c1772, c1738, c264, c1770, c197, c268, c539, c68, c61, c75, c254, c194, c97, c252, c1773, c1731, c140, c360, c276, c233, c134] c1774 unsat1774 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1765 := derived1765 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c1766 := derived1766 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c1772 := derived1772 a h
  have h7 : Entails.eval a c1738 := derived1738 a h
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c1770 := derived1770 a h
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c539 := derived539 a h
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c254 := h 253 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c252 := h 251 (by decide)
  have h20 : Entails.eval a c1773 := derived1773 a h
  have h21 : Entails.eval a c1731 := derived1731 a h
  have h22 : Entails.eval a c140 := h 139 (by decide)
  have h23 : Entails.eval a c360 := h 359 (by decide)
  have h24 : Entails.eval a c276 := h 275 (by decide)
  have h25 : Entails.eval a c233 := h 232 (by decide)
  have h26 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1775 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1765, some c2, some c264, some c13, some c1766, some c12, some c1770, some c1774, some c25, some c539, some c166, some c63, some c260, some c194, some c103, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1775 : lratChecker f1775 p1775 = .success := by decide +kernel
theorem unsat1775 : Unsatisfiable (PosFin 57) f1775 := by
  apply lratCheckerSound f1775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1775
  · intro a ha; simp [p1775] at ha; subst a; trivial
  · exact checked1775
theorem derived1775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1775 := by
  apply localUnsat_implies_entails f1775 [c1738, c1632, c1765, c2, c264, c13, c1766, c12, c1770, c1774, c25, c539, c166, c63, c260, c194, c103] c1775 unsat1775 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1765 := derived1765 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c1766 := derived1766 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c1770 := derived1770 a h
  have h9 : Entails.eval a c1774 := derived1774 a h
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c539 := derived539 a h
  have h12 : Entails.eval a c166 := h 165 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1776 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1765, some c2, some c264, some c13, some c1766, some c12, some c1770, some c266, some c1775, some c106, some c1219, some c38, some c268, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1776 : lratChecker f1776 p1776 = .success := by decide +kernel
theorem unsat1776 : Unsatisfiable (PosFin 57) f1776 := by
  apply lratCheckerSound f1776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1776
  · intro a ha; simp [p1776] at ha; subst a; trivial
  · exact checked1776
theorem derived1776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1776 := by
  apply localUnsat_implies_entails f1776 [c1738, c1632, c1765, c2, c264, c13, c1766, c12, c1770, c266, c1775, c106, c1219, c38, c268] c1776 unsat1776 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1765 := derived1765 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c1766 := derived1766 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c1770 := derived1770 a h
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c1775 := derived1775 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c1219 := derived1219 a h
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1777 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c87, some c173, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1777 : lratChecker f1777 p1777 = .success := by decide +kernel
theorem unsat1777 : Unsatisfiable (PosFin 57) f1777 := by
  apply lratCheckerSound f1777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1777
  · intro a ha; simp [p1777] at ha; subst a; trivial
  · exact checked1777
theorem derived1777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1777 := by
  apply localUnsat_implies_entails f1777 [c233, c87, c173] c1777 unsat1777 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1778 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨47, by decide⟩, false), (⟨43, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c1147, some c244, some c198, some c175, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1778 : lratChecker f1778 p1778 = .success := by decide +kernel
theorem unsat1778 : Unsatisfiable (PosFin 57) f1778 := by
  apply lratCheckerSound f1778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1778
  · intro a ha; simp [p1778] at ha; subst a; trivial
  · exact checked1778
theorem derived1778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1778 := by
  apply localUnsat_implies_entails f1778 [c266, c1147, c244, c198, c175] c1778 unsat1778 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1779 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1776, some c105, some c107, some c1632, some c1765, some c2, some c1738, some c1777, some c135, some c51, some c139, some c119, some c1427, some c268, some c1778, some c39, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1779 : lratChecker f1779 p1779 = .success := by decide +kernel
theorem unsat1779 : Unsatisfiable (PosFin 57) f1779 := by
  apply lratCheckerSound f1779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1779
  · intro a ha; simp [p1779] at ha; subst a; trivial
  · exact checked1779
theorem derived1779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1779 := by
  apply localUnsat_implies_entails f1779 [c1776, c105, c107, c1632, c1765, c2, c1738, c1777, c135, c51, c139, c119, c1427, c268, c1778, c39] c1779 unsat1779 (by rfl) a
  have h0 : Entails.eval a c1776 := derived1776 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c1765 := derived1765 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c1777 := derived1777 a h
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c1427 := derived1427 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c1778 := derived1778 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1780 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c2, some c264, some c135, some c142, some c233, some c43, some c134, some c216, some c212, some c316, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1780 : lratChecker f1780 p1780 = .success := by decide +kernel
theorem unsat1780 : Unsatisfiable (PosFin 57) f1780 := by
  apply lratCheckerSound f1780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1780
  · intro a ha; simp [p1780] at ha; subst a; trivial
  · exact checked1780
theorem derived1780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1780 := by
  apply localUnsat_implies_entails f1780 [c1738, c1632, c2, c264, c135, c142, c233, c43, c134, c216, c212, c316] c1780 unsat1780 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1781 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1776, some c105, some c107, some c1779, some c1137, some c1738, some c1632, some c1765, some c2, some c264, some c1780, some c51, some c216, some c212, some c49, some c315, some c1229, some c141, some c26, some c42, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1781 : lratChecker f1781 p1781 = .success := by decide +kernel
theorem unsat1781 : Unsatisfiable (PosFin 57) f1781 := by
  apply lratCheckerSound f1781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1781
  · intro a ha; simp [p1781] at ha; subst a; trivial
  · exact checked1781
theorem derived1781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1781 := by
  apply localUnsat_implies_entails f1781 [c1147, c1776, c105, c107, c1779, c1137, c1738, c1632, c1765, c2, c264, c1780, c51, c216, c212, c49, c315, c1229, c141, c26, c42] c1781 unsat1781 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1776 := derived1776 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c1779 := derived1779 a h
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1738 := derived1738 a h
  have h7 : Entails.eval a c1632 := derived1632 a h
  have h8 : Entails.eval a c1765 := derived1765 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1780 := derived1780 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c1229 := derived1229 a h
  have h18 : Entails.eval a c141 := h 140 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1782 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1776, some c105, some c107, some c1779, some c1137, some c1632, some c1765, some c12, some c1738, some c2, some c264, some c1781, some c268, some c1723, some c25, some c38, some c123, some c113, some c164, some c42, some c219, some c214, some c269, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1782 : lratChecker f1782 p1782 = .success := by decide +kernel
theorem unsat1782 : Unsatisfiable (PosFin 57) f1782 := by
  apply lratCheckerSound f1782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1782
  · intro a ha; simp [p1782] at ha; subst a; trivial
  · exact checked1782
theorem derived1782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1782 := by
  apply localUnsat_implies_entails f1782 [c1776, c105, c107, c1779, c1137, c1632, c1765, c12, c1738, c2, c264, c1781, c268, c1723, c25, c38, c123, c113, c164, c42, c219, c214, c269] c1782 unsat1782 (by rfl) a
  have h0 : Entails.eval a c1776 := derived1776 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c1779 := derived1779 a h
  have h4 : Entails.eval a c1137 := derived1137 a h
  have h5 : Entails.eval a c1632 := derived1632 a h
  have h6 : Entails.eval a c1765 := derived1765 a h
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c1738 := derived1738 a h
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1781 := derived1781 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c1723 := derived1723 a h
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c219 := h 218 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1783 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c49, some c212, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1783 : lratChecker f1783 p1783 = .success := by decide +kernel
theorem unsat1783 : Unsatisfiable (PosFin 57) f1783 := by
  apply lratCheckerSound f1783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1783
  · intro a ha; simp [p1783] at ha; subst a; trivial
  · exact checked1783
theorem derived1783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1783 := by
  apply localUnsat_implies_entails f1783 [c51, c49, c212] c1783 unsat1783 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1784 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1765, some c2, some c264, some c1776, some c107, some c105, some c1779, some c1137, some c1427, some c1782, some c266, some c1299, some c8, some c39, some c28, some c268, some c168, some c224, some c1783, some c135, some c142, some c233, some c85, some c43, some c169, some c134, some c292, some c274, some c316, some c58, some c146, some c296, some c251, some c167, some c78, some c62, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked1784 : lratChecker f1784 p1784 = .success := by decide +kernel
theorem unsat1784 : Unsatisfiable (PosFin 57) f1784 := by
  apply lratCheckerSound f1784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1784
  · intro a ha; simp [p1784] at ha; subst a; trivial
  · exact checked1784
theorem derived1784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1784 := by
  apply localUnsat_implies_entails f1784 [c1738, c1632, c1765, c2, c264, c1776, c107, c105, c1779, c1137, c1427, c1782, c266, c1299, c8, c39, c28, c268, c168, c224, c1783, c135, c142, c233, c85, c43, c169, c134, c292, c274, c316, c58, c146, c296, c251, c167, c78, c62] c1784 unsat1784 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1765 := derived1765 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c1776 := derived1776 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c1779 := derived1779 a h
  have h9 : Entails.eval a c1137 := derived1137 a h
  have h10 : Entails.eval a c1427 := derived1427 a h
  have h11 : Entails.eval a c1782 := derived1782 a h
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c1299 := derived1299 a h
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c168 := h 167 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  have h20 : Entails.eval a c1783 := derived1783 a h
  have h21 : Entails.eval a c135 := h 134 (by decide)
  have h22 : Entails.eval a c142 := h 141 (by decide)
  have h23 : Entails.eval a c233 := h 232 (by decide)
  have h24 : Entails.eval a c85 := h 84 (by decide)
  have h25 : Entails.eval a c43 := h 42 (by decide)
  have h26 : Entails.eval a c169 := h 168 (by decide)
  have h27 : Entails.eval a c134 := h 133 (by decide)
  have h28 : Entails.eval a c292 := h 291 (by decide)
  have h29 : Entails.eval a c274 := h 273 (by decide)
  have h30 : Entails.eval a c316 := h 315 (by decide)
  have h31 : Entails.eval a c58 := h 57 (by decide)
  have h32 : Entails.eval a c146 := h 145 (by decide)
  have h33 : Entails.eval a c296 := h 295 (by decide)
  have h34 : Entails.eval a c251 := h 250 (by decide)
  have h35 : Entails.eval a c167 := h 166 (by decide)
  have h36 : Entails.eval a c78 := h 77 (by decide)
  have h37 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1785 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨51, by decide⟩, true), (⟨35, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1784, some c111, some c1373, some c16, some c1632, some c113, some c1702, some c1294, some c335, some c106, some c183, some c97, some c104, some c100, some c378, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1785 : lratChecker f1785 p1785 = .success := by decide +kernel
theorem unsat1785 : Unsatisfiable (PosFin 57) f1785 := by
  apply lratCheckerSound f1785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1785
  · intro a ha; simp [p1785] at ha; subst a; trivial
  · exact checked1785
theorem derived1785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1785 := by
  apply localUnsat_implies_entails f1785 [c1784, c111, c1373, c16, c1632, c113, c1702, c1294, c335, c106, c183, c97, c104, c100, c378] c1785 unsat1785 (by rfl) a
  have h0 : Entails.eval a c1784 := derived1784 a h
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c1373 := derived1373 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c1702 := derived1702 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c335 := h 334 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1786 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1784, some c200, some c1738, some c1632, some c22, some c33, some c1754, some c157, some c268, some c111, some c16, some c1373, some c1083, some c117, some c1597, some c41, some c1785, some c263, some c885, some c131, some c1562, some c202, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1786 : lratChecker f1786 p1786 = .success := by decide +kernel
theorem unsat1786 : Unsatisfiable (PosFin 57) f1786 := by
  apply lratCheckerSound f1786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1786
  · intro a ha; simp [p1786] at ha; subst a; trivial
  · exact checked1786
theorem derived1786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1786 := by
  apply localUnsat_implies_entails f1786 [c1784, c200, c1738, c1632, c22, c33, c1754, c157, c268, c111, c16, c1373, c1083, c117, c1597, c41, c1785, c263, c885, c131, c1562, c202] c1786 unsat1786 (by rfl) a
  have h0 : Entails.eval a c1784 := derived1784 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c1754 := derived1754 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c1373 := derived1373 a h
  have h12 : Entails.eval a c1083 := derived1083 a h
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c1597 := derived1597 a h
  have h15 : Entails.eval a c41 := h 40 (by decide)
  have h16 : Entails.eval a c1785 := derived1785 a h
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c885 := derived885 a h
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c1562 := derived1562 a h
  have h21 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1787 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c4, some c1744, some c128, some c5, some c25, some c446, some c263, some c280, some c123, some c219, some c153, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1787 : lratChecker f1787 p1787 = .success := by decide +kernel
theorem unsat1787 : Unsatisfiable (PosFin 57) f1787 := by
  apply lratCheckerSound f1787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1787
  · intro a ha; simp [p1787] at ha; subst a; trivial
  · exact checked1787
theorem derived1787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1787 := by
  apply localUnsat_implies_entails f1787 [c116, c4, c1744, c128, c5, c25, c446, c263, c280, c123, c219, c153] c1787 unsat1787 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c1744 := derived1744 a h
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c446 := derived446 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1788 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c264, some c200, some c266, some c1147, some c202, some c1787, some c204, some c1216, some c19, some c1219, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1788 : lratChecker f1788 p1788 = .success := by decide +kernel
theorem unsat1788 : Unsatisfiable (PosFin 57) f1788 := by
  apply lratCheckerSound f1788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1788
  · intro a ha; simp [p1788] at ha; subst a; trivial
  · exact checked1788
theorem derived1788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1788 := by
  apply localUnsat_implies_entails f1788 [c1738, c264, c200, c266, c1147, c202, c1787, c204, c1216, c19, c1219] c1788 unsat1788 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c1787 := derived1787 a h
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c1216 := derived1216 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c1219 := derived1219 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1789 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1744, some c20, some c39, some c106, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1789 : lratChecker f1789 p1789 = .success := by decide +kernel
theorem unsat1789 : Unsatisfiable (PosFin 57) f1789 := by
  apply lratCheckerSound f1789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1789
  · intro a ha; simp [p1789] at ha; subst a; trivial
  · exact checked1789
theorem derived1789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1789 := by
  apply localUnsat_implies_entails f1789 [c1738, c1744, c20, c39, c106] c1789 unsat1789 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1744 := derived1744 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1790 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1784, some c200, some c1738, some c1786, some c264, some c4, some c111, some c1788, some c896, some c1789, some c1770, some c1708, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1790 : lratChecker f1790 p1790 = .success := by decide +kernel
theorem unsat1790 : Unsatisfiable (PosFin 57) f1790 := by
  apply lratCheckerSound f1790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1790
  · intro a ha; simp [p1790] at ha; subst a; trivial
  · exact checked1790
theorem derived1790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1790 := by
  apply localUnsat_implies_entails f1790 [c1784, c200, c1738, c1786, c264, c4, c111, c1788, c896, c1789, c1770, c1708] c1790 unsat1790 (by rfl) a
  have h0 : Entails.eval a c1784 := derived1784 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c1738 := derived1738 a h
  have h3 : Entails.eval a c1786 := derived1786 a h
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c1788 := derived1788 a h
  have h8 : Entails.eval a c896 := derived896 a h
  have h9 : Entails.eval a c1789 := derived1789 a h
  have h10 : Entails.eval a c1770 := derived1770 a h
  have h11 : Entails.eval a c1708 := derived1708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1791 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c1738, some c1632, some c22, some c32, some c982, some c267, some c1744, some c204, some c1137, some c19, some c123, some c202, some c262, some c1147, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1791 : lratChecker f1791 p1791 = .success := by decide +kernel
theorem unsat1791 : Unsatisfiable (PosFin 57) f1791 := by
  apply lratCheckerSound f1791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1791
  · intro a ha; simp [p1791] at ha; subst a; trivial
  · exact checked1791
theorem derived1791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1791 := by
  apply localUnsat_implies_entails f1791 [c200, c1738, c1632, c22, c32, c982, c267, c1744, c204, c1137, c19, c123, c202, c262, c1147] c1791 unsat1791 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c982 := derived982 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c1744 := derived1744 a h
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c1137 := derived1137 a h
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c1147 := derived1147 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1792 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1784, some c1738, some c200, some c1790, some c107, some c105, some c1791, some c264, some c1788, some c896, some c39, some c1744, some c204, some c1708, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1792 : lratChecker f1792 p1792 = .success := by decide +kernel
theorem unsat1792 : Unsatisfiable (PosFin 57) f1792 := by
  apply lratCheckerSound f1792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1792
  · intro a ha; simp [p1792] at ha; subst a; trivial
  · exact checked1792
theorem derived1792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1792 := by
  apply localUnsat_implies_entails f1792 [c1784, c1738, c200, c1790, c107, c105, c1791, c264, c1788, c896, c39, c1744, c204, c1708] c1792 unsat1792 (by rfl) a
  have h0 : Entails.eval a c1784 := derived1784 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c1790 := derived1790 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1791 := derived1791 a h
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c1788 := derived1788 a h
  have h9 : Entails.eval a c896 := derived896 a h
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c1744 := derived1744 a h
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c1708 := derived1708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1793 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1793 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1792, some c2, some c264, some c1784, some c13, some c204, some c12, some c111, some c1296, some c1613, some c1192, some c117, some c266, some c1299, some c41, some c885, some c133, some c1376, some c113, some c80, some c77, some c230, some c172, some c233, some c291, some c290, some c317, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1793 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1793 : lratChecker f1793 p1793 = .success := by decide +kernel
theorem unsat1793 : Unsatisfiable (PosFin 57) f1793 := by
  apply lratCheckerSound f1793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1793
  · intro a ha; simp [p1793] at ha; subst a; trivial
  · exact checked1793
theorem derived1793 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1793 := by
  apply localUnsat_implies_entails f1793 [c1738, c1632, c1792, c2, c264, c1784, c13, c204, c12, c111, c1296, c1613, c1192, c117, c266, c1299, c41, c885, c133, c1376, c113, c80, c77, c230, c172, c233, c291, c290, c317] c1793 unsat1793 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1792 := derived1792 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c1784 := derived1784 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c1296 := derived1296 a h
  have h11 : Entails.eval a c1613 := derived1613 a h
  have h12 : Entails.eval a c1192 := derived1192 a h
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c1299 := derived1299 a h
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c885 := derived885 a h
  have h18 : Entails.eval a c133 := h 132 (by decide)
  have h19 : Entails.eval a c1376 := derived1376 a h
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c77 := h 76 (by decide)
  have h23 : Entails.eval a c230 := h 229 (by decide)
  have h24 : Entails.eval a c172 := h 171 (by decide)
  have h25 : Entails.eval a c233 := h 232 (by decide)
  have h26 : Entails.eval a c291 := h 290 (by decide)
  have h27 : Entails.eval a c290 := h 289 (by decide)
  have h28 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1794 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1794 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1784, some c1792, some c2, some c264, some c1793, some c107, some c105, some c12, some c204, some c203, some c1744, some c39, some c266, some c1787, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1794 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1794 : lratChecker f1794 p1794 = .success := by decide +kernel
theorem unsat1794 : Unsatisfiable (PosFin 57) f1794 := by
  apply lratCheckerSound f1794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1794
  · intro a ha; simp [p1794] at ha; subst a; trivial
  · exact checked1794
theorem derived1794 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1794 := by
  apply localUnsat_implies_entails f1794 [c1738, c1632, c1784, c1792, c2, c264, c1793, c107, c105, c12, c204, c203, c1744, c39, c266, c1787] c1794 unsat1794 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1784 := derived1784 a h
  have h3 : Entails.eval a c1792 := derived1792 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c1793 := derived1793 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c1744 := derived1744 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c1787 := derived1787 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1795 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1795 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c33, some c22, some c1794, some c15, some c1634, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1795 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1795 : lratChecker f1795 p1795 = .success := by decide +kernel
theorem unsat1795 : Unsatisfiable (PosFin 57) f1795 := by
  apply lratCheckerSound f1795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1795
  · intro a ha; simp [p1795] at ha; subst a; trivial
  · exact checked1795
theorem derived1795 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1795 := by
  apply localUnsat_implies_entails f1795 [c1632, c33, c22, c1794, c15, c1634] c1795 unsat1795 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1794 := derived1794 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1634 := derived1634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1796 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1796 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c22, some c1795, some c106, some c1678, some c1794, some c14, some c159, some c62, some c259, some c33, some c263, some c1738, some c187, some c97, some c255, some c70, some c76, some c353, some c349, some c201, some c202, some c268, some c1754, some c1332, some c1473, some c273, some c135, some c147, some c239, some c324, some c44, some c317, some c276, some c139, some c176, some c142, some c342, some c344, some c237, some c88, some c182, some c309, some c207, some c219, some c354, some c117, some c294, some c80, some c404, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1796 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]]
theorem checked1796 : lratChecker f1796 p1796 = .success := by decide +kernel
theorem unsat1796 : Unsatisfiable (PosFin 57) f1796 := by
  apply lratCheckerSound f1796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1796
  · intro a ha; simp [p1796] at ha; subst a; trivial
  · exact checked1796
theorem derived1796 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1796 := by
  apply localUnsat_implies_entails f1796 [c1632, c22, c1795, c106, c1678, c1794, c14, c159, c62, c259, c33, c263, c1738, c187, c97, c255, c70, c76, c353, c349, c201, c202, c268, c1754, c1332, c1473, c273, c135, c147, c239, c324, c44, c317, c276, c139, c176, c142, c342, c344, c237, c88, c182, c309, c207, c219, c354, c117, c294, c80, c404] c1796 unsat1796 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1795 := derived1795 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1678 := derived1678 a h
  have h5 : Entails.eval a c1794 := derived1794 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c259 := h 258 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c1738 := derived1738 a h
  have h13 : Entails.eval a c187 := h 186 (by decide)
  have h14 : Entails.eval a c97 := h 96 (by decide)
  have h15 : Entails.eval a c255 := h 254 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c76 := h 75 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c201 := h 200 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c268 := h 267 (by decide)
  have h23 : Entails.eval a c1754 := derived1754 a h
  have h24 : Entails.eval a c1332 := derived1332 a h
  have h25 : Entails.eval a c1473 := derived1473 a h
  have h26 : Entails.eval a c273 := h 272 (by decide)
  have h27 : Entails.eval a c135 := h 134 (by decide)
  have h28 : Entails.eval a c147 := h 146 (by decide)
  have h29 : Entails.eval a c239 := h 238 (by decide)
  have h30 : Entails.eval a c324 := h 323 (by decide)
  have h31 : Entails.eval a c44 := h 43 (by decide)
  have h32 : Entails.eval a c317 := h 316 (by decide)
  have h33 : Entails.eval a c276 := h 275 (by decide)
  have h34 : Entails.eval a c139 := h 138 (by decide)
  have h35 : Entails.eval a c176 := h 175 (by decide)
  have h36 : Entails.eval a c142 := h 141 (by decide)
  have h37 : Entails.eval a c342 := h 341 (by decide)
  have h38 : Entails.eval a c344 := h 343 (by decide)
  have h39 : Entails.eval a c237 := h 236 (by decide)
  have h40 : Entails.eval a c88 := h 87 (by decide)
  have h41 : Entails.eval a c182 := h 181 (by decide)
  have h42 : Entails.eval a c309 := h 308 (by decide)
  have h43 : Entails.eval a c207 := h 206 (by decide)
  have h44 : Entails.eval a c219 := h 218 (by decide)
  have h45 : Entails.eval a c354 := h 353 (by decide)
  have h46 : Entails.eval a c117 := h 116 (by decide)
  have h47 : Entails.eval a c294 := h 293 (by decide)
  have h48 : Entails.eval a c80 := h 79 (by decide)
  have h49 : Entails.eval a c404 := h 403 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1797 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨35, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1797 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c22, some c44, some c41, some c147, some c208, some c273, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1797 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1797 : lratChecker f1797 p1797 = .success := by decide +kernel
theorem unsat1797 : Unsatisfiable (PosFin 57) f1797 := by
  apply lratCheckerSound f1797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1797
  · intro a ha; simp [p1797] at ha; subst a; trivial
  · exact checked1797
theorem derived1797 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1797 := by
  apply localUnsat_implies_entails f1797 [c1632, c22, c44, c41, c147, c208, c273] c1797 unsat1797 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1798 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1798 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1754, some c1738, some c1632, some c33, some c268, some c1795, some c1794, some c106, some c14, some c202, some c22, some c159, some c70, some c1797, some c62, some c187, some c97, some c255, some c349, some c76, some c1678, some c263, some c1796, some c113, some c182, some c155, some c219, some c457, some c257, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1798 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1798 : lratChecker f1798 p1798 = .success := by decide +kernel
theorem unsat1798 : Unsatisfiable (PosFin 57) f1798 := by
  apply lratCheckerSound f1798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1798
  · intro a ha; simp [p1798] at ha; subst a; trivial
  · exact checked1798
theorem derived1798 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1798 := by
  apply localUnsat_implies_entails f1798 [c1754, c1738, c1632, c33, c268, c1795, c1794, c106, c14, c202, c22, c159, c70, c1797, c62, c187, c97, c255, c349, c76, c1678, c263, c1796, c113, c182, c155, c219, c457, c257] c1798 unsat1798 (by rfl) a
  have h0 : Entails.eval a c1754 := derived1754 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1795 := derived1795 a h
  have h6 : Entails.eval a c1794 := derived1794 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c1797 := derived1797 a h
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c187 := h 186 (by decide)
  have h16 : Entails.eval a c97 := h 96 (by decide)
  have h17 : Entails.eval a c255 := h 254 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c76 := h 75 (by decide)
  have h20 : Entails.eval a c1678 := derived1678 a h
  have h21 : Entails.eval a c263 := h 262 (by decide)
  have h22 : Entails.eval a c1796 := derived1796 a h
  have h23 : Entails.eval a c113 := h 112 (by decide)
  have h24 : Entails.eval a c182 := h 181 (by decide)
  have h25 : Entails.eval a c155 := h 154 (by decide)
  have h26 : Entails.eval a c219 := h 218 (by decide)
  have h27 : Entails.eval a c457 := derived457 a h
  have h28 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1799 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1632, some c22, some c33, some c1754, some c268, some c1795, some c106, some c1678, some c14, some c202, some c159, some c70, some c62, some c76, some c187, some c353, some c97, some c255, some c1797, some c1798, some c120, some c227, some c896, some c348, some c276, some c257, some c205, some c457, some c246, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1799 : lratChecker f1799 p1799 = .success := by decide +kernel
theorem unsat1799 : Unsatisfiable (PosFin 57) f1799 := by
  apply lratCheckerSound f1799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1799
  · intro a ha; simp [p1799] at ha; subst a; trivial
  · exact checked1799
theorem derived1799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1799 := by
  apply localUnsat_implies_entails f1799 [c1794, c1738, c1632, c22, c33, c1754, c268, c1795, c106, c1678, c14, c202, c159, c70, c62, c76, c187, c353, c97, c255, c1797, c1798, c120, c227, c896, c348, c276, c257, c205, c457, c246] c1799 unsat1799 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c1754 := derived1754 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1795 := derived1795 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c1678 := derived1678 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c255 := h 254 (by decide)
  have h20 : Entails.eval a c1797 := derived1797 a h
  have h21 : Entails.eval a c1798 := derived1798 a h
  have h22 : Entails.eval a c120 := h 119 (by decide)
  have h23 : Entails.eval a c227 := h 226 (by decide)
  have h24 : Entails.eval a c896 := derived896 a h
  have h25 : Entails.eval a c348 := h 347 (by decide)
  have h26 : Entails.eval a c276 := h 275 (by decide)
  have h27 : Entails.eval a c257 := h 256 (by decide)
  have h28 : Entails.eval a c205 := h 204 (by decide)
  have h29 : Entails.eval a c457 := derived457 a h
  have h30 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1800 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1799, some c264, some c1794, some c1147, some c202, some c201, some c15, some c4, some c116, some c106, some c1219, some c1611, some c1261, some c1485, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1800 : lratChecker f1800 p1800 = .success := by decide +kernel
theorem unsat1800 : Unsatisfiable (PosFin 57) f1800 := by
  apply lratCheckerSound f1800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1800
  · intro a ha; simp [p1800] at ha; subst a; trivial
  · exact checked1800
theorem derived1800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1800 := by
  apply localUnsat_implies_entails f1800 [c1738, c1799, c264, c1794, c1147, c202, c201, c15, c4, c116, c106, c1219, c1611, c1261, c1485] c1800 unsat1800 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1799 := derived1799 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c1794 := derived1794 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c1219 := derived1219 a h
  have h12 : Entails.eval a c1611 := derived1611 a h
  have h13 : Entails.eval a c1261 := derived1261 a h
  have h14 : Entails.eval a c1485 := derived1485 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1801 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1632, some c1799, some c1800, some c266, some c1348, some c14, some c106, some c1565, some c15, some c28, some c501, some c249, some c188, some c99, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1801 : lratChecker f1801 p1801 = .success := by decide +kernel
theorem unsat1801 : Unsatisfiable (PosFin 57) f1801 := by
  apply lratCheckerSound f1801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1801
  · intro a ha; simp [p1801] at ha; subst a; trivial
  · exact checked1801
theorem derived1801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1801 := by
  apply localUnsat_implies_entails f1801 [c1794, c1738, c1632, c1799, c1800, c266, c1348, c14, c106, c1565, c15, c28, c501, c249, c188, c99] c1801 unsat1801 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1799 := derived1799 a h
  have h4 : Entails.eval a c1800 := derived1800 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c1348 := derived1348 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c1565 := derived1565 a h
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c501 := derived501 a h
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1802 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1632, some c22, some c32, some c160, some c268, some c267, some c71, some c75, some c1615, some c353, some c224, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1802 : lratChecker f1802 p1802 = .success := by decide +kernel
theorem unsat1802 : Unsatisfiable (PosFin 57) f1802 := by
  apply lratCheckerSound f1802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1802
  · intro a ha; simp [p1802] at ha; subst a; trivial
  · exact checked1802
theorem derived1802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1802 := by
  apply localUnsat_implies_entails f1802 [c1794, c1738, c1632, c22, c32, c160, c268, c267, c71, c75, c1615, c353, c224] c1802 unsat1802 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c1615 := derived1615 a h
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1803 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1632, some c1801, some c107, some c105, some c15, some c202, some c1147, some c1802, some c266, some c982, some c58, some c249, some c188, some c99, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1803 : lratChecker f1803 p1803 = .success := by decide +kernel
theorem unsat1803 : Unsatisfiable (PosFin 57) f1803 := by
  apply lratCheckerSound f1803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1803
  · intro a ha; simp [p1803] at ha; subst a; trivial
  · exact checked1803
theorem derived1803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1803 := by
  apply localUnsat_implies_entails f1803 [c1794, c1738, c1632, c1801, c107, c105, c15, c202, c1147, c1802, c266, c982, c58, c249, c188, c99] c1803 unsat1803 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1801 := derived1801 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c1802 := derived1802 a h
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c982 := derived982 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c249 := h 248 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1804 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1803, some c1632, some c13, some c2, some c1794, some c1738, some c15, some c1564, some c64, some c252, some c196, some c97, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1804 : lratChecker f1804 p1804 = .success := by decide +kernel
theorem unsat1804 : Unsatisfiable (PosFin 57) f1804 := by
  apply lratCheckerSound f1804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1804
  · intro a ha; simp [p1804] at ha; subst a; trivial
  · exact checked1804
theorem derived1804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1804 := by
  apply localUnsat_implies_entails f1804 [c1803, c1632, c13, c2, c1794, c1738, c15, c1564, c64, c252, c196, c97] c1804 unsat1804 (by rfl) a
  have h0 : Entails.eval a c1803 := derived1803 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c1794 := derived1794 a h
  have h5 : Entails.eval a c1738 := derived1738 a h
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c1564 := derived1564 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c196 := h 195 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1805 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1803, some c1632, some c13, some c1738, some c2, some c264, some c266, some c1804, some c106, some c1219, some c1501, some c26, some c1335, some c268, some c123, some c113, some c38, some c1614, some c41, some c219, some c214, some c270, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1805 : lratChecker f1805 p1805 = .success := by decide +kernel
theorem unsat1805 : Unsatisfiable (PosFin 57) f1805 := by
  apply lratCheckerSound f1805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1805
  · intro a ha; simp [p1805] at ha; subst a; trivial
  · exact checked1805
theorem derived1805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1805 := by
  apply localUnsat_implies_entails f1805 [c1803, c1632, c13, c1738, c2, c264, c266, c1804, c106, c1219, c1501, c26, c1335, c268, c123, c113, c38, c1614, c41, c219, c214, c270] c1805 unsat1805 (by rfl) a
  have h0 : Entails.eval a c1803 := derived1803 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c1738 := derived1738 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c1804 := derived1804 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c1219 := derived1219 a h
  have h10 : Entails.eval a c1501 := derived1501 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c1335 := derived1335 a h
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c1614 := derived1614 a h
  have h18 : Entails.eval a c41 := h 40 (by decide)
  have h19 : Entails.eval a c219 := h 218 (by decide)
  have h20 : Entails.eval a c214 := h 213 (by decide)
  have h21 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1806 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨36, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1632, some c70, some c62, some c349, some c251, some c58, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1806 : lratChecker f1806 p1806 = .success := by decide +kernel
theorem unsat1806 : Unsatisfiable (PosFin 57) f1806 := by
  apply lratCheckerSound f1806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1806
  · intro a ha; simp [p1806] at ha; subst a; trivial
  · exact checked1806
theorem derived1806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1806 := by
  apply localUnsat_implies_entails f1806 [c1794, c1632, c70, c62, c349, c251, c58] c1806 unsat1806 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1807 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c249, some c251, some c98, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1807 : lratChecker f1807 p1807 = .success := by decide +kernel
theorem unsat1807 : Unsatisfiable (PosFin 57) f1807 := by
  apply lratCheckerSound f1807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1807
  · intro a ha; simp [p1807] at ha; subst a; trivial
  · exact checked1807
theorem derived1807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1807 := by
  apply localUnsat_implies_entails f1807 [c1794, c1738, c249, c251, c98] c1807 unsat1807 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1808 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1632, some c1807, some c58, some c1806, some c350, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1808 : lratChecker f1808 p1808 = .success := by decide +kernel
theorem unsat1808 : Unsatisfiable (PosFin 57) f1808 := by
  apply lratCheckerSound f1808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1808
  · intro a ha; simp [p1808] at ha; subst a; trivial
  · exact checked1808
theorem derived1808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1808 := by
  apply localUnsat_implies_entails f1808 [c1632, c1807, c58, c1806, c350] c1808 unsat1808 (by rfl) a
  have h0 : Entails.eval a c1632 := derived1632 a h
  have h1 : Entails.eval a c1807 := derived1807 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c1806 := derived1806 a h
  have h4 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1809 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨39, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c264, some c1632, some c1807, some c58, some c1808, some c225, some c351, some c168, some c348, some c62, some c1498, some c219, some c193, some c246, some c336, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1809 : lratChecker f1809 p1809 = .success := by decide +kernel
theorem unsat1809 : Unsatisfiable (PosFin 57) f1809 := by
  apply lratCheckerSound f1809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1809
  · intro a ha; simp [p1809] at ha; subst a; trivial
  · exact checked1809
theorem derived1809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1809 := by
  apply localUnsat_implies_entails f1809 [c1738, c264, c1632, c1807, c58, c1808, c225, c351, c168, c348, c62, c1498, c219, c193, c246, c336] c1809 unsat1809 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1807 := derived1807 a h
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c1808 := derived1808 a h
  have h6 : Entails.eval a c225 := h 224 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c1498 := derived1498 a h
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1810 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1738, some c1803, some c1632, some c13, some c1805, some c1565, some c106, some c14, some c2, some c264, some c1769, some c1809, some c26, some c1219, some c268, some c1386, some c166, some c227, some c167, some c1501, some c120, some c44, some c133, some c80, some c175, some c284, some c727, some c141, some c142, some c315, some c292, some c369, some c113, some c129, some c1614, some c347, some c351, some c58, some c249, some c98, some c193, some c336, some c247, some c900, some c379, some c283, some c924, some c59, some c1613, some c77, some c364, some c405, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53]]
theorem checked1810 : lratChecker f1810 p1810 = .success := by decide +kernel
theorem unsat1810 : Unsatisfiable (PosFin 57) f1810 := by
  apply lratCheckerSound f1810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1810
  · intro a ha; simp [p1810] at ha; subst a; trivial
  · exact checked1810
theorem derived1810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1810 := by
  apply localUnsat_implies_entails f1810 [c1794, c1738, c1803, c1632, c13, c1805, c1565, c106, c14, c2, c264, c1769, c1809, c26, c1219, c268, c1386, c166, c227, c167, c1501, c120, c44, c133, c80, c175, c284, c727, c141, c142, c315, c292, c369, c113, c129, c1614, c347, c351, c58, c249, c98, c193, c336, c247, c900, c379, c283, c924, c59, c1613, c77, c364, c405] c1810 unsat1810 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1738 := derived1738 a h
  have h2 : Entails.eval a c1803 := derived1803 a h
  have h3 : Entails.eval a c1632 := derived1632 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c1805 := derived1805 a h
  have h6 : Entails.eval a c1565 := derived1565 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c1769 := derived1769 a h
  have h12 : Entails.eval a c1809 := derived1809 a h
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c1219 := derived1219 a h
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c1386 := derived1386 a h
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c227 := h 226 (by decide)
  have h19 : Entails.eval a c167 := h 166 (by decide)
  have h20 : Entails.eval a c1501 := derived1501 a h
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c44 := h 43 (by decide)
  have h23 : Entails.eval a c133 := h 132 (by decide)
  have h24 : Entails.eval a c80 := h 79 (by decide)
  have h25 : Entails.eval a c175 := h 174 (by decide)
  have h26 : Entails.eval a c284 := h 283 (by decide)
  have h27 : Entails.eval a c727 := derived727 a h
  have h28 : Entails.eval a c141 := h 140 (by decide)
  have h29 : Entails.eval a c142 := h 141 (by decide)
  have h30 : Entails.eval a c315 := h 314 (by decide)
  have h31 : Entails.eval a c292 := h 291 (by decide)
  have h32 : Entails.eval a c369 := h 368 (by decide)
  have h33 : Entails.eval a c113 := h 112 (by decide)
  have h34 : Entails.eval a c129 := h 128 (by decide)
  have h35 : Entails.eval a c1614 := derived1614 a h
  have h36 : Entails.eval a c347 := h 346 (by decide)
  have h37 : Entails.eval a c351 := h 350 (by decide)
  have h38 : Entails.eval a c58 := h 57 (by decide)
  have h39 : Entails.eval a c249 := h 248 (by decide)
  have h40 : Entails.eval a c98 := h 97 (by decide)
  have h41 : Entails.eval a c193 := h 192 (by decide)
  have h42 : Entails.eval a c336 := h 335 (by decide)
  have h43 : Entails.eval a c247 := h 246 (by decide)
  have h44 : Entails.eval a c900 := derived900 a h
  have h45 : Entails.eval a c379 := h 378 (by decide)
  have h46 : Entails.eval a c283 := h 282 (by decide)
  have h47 : Entails.eval a c924 := derived924 a h
  have h48 : Entails.eval a c59 := h 58 (by decide)
  have h49 : Entails.eval a c1613 := derived1613 a h
  have h50 : Entails.eval a c77 := h 76 (by decide)
  have h51 : Entails.eval a c364 := h 363 (by decide)
  have h52 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1811 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1738, some c1632, some c1803, some c2, some c264, some c1794, some c13, some c1805, some c1565, some c106, some c1769, some c14, some c1809, some c1386, some c1810, some c1770, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1811 : lratChecker f1811 p1811 = .success := by decide +kernel
theorem unsat1811 : Unsatisfiable (PosFin 57) f1811 := by
  apply lratCheckerSound f1811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1811
  · intro a ha; simp [p1811] at ha; subst a; trivial
  · exact checked1811
theorem derived1811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1811 := by
  apply localUnsat_implies_entails f1811 [c1738, c1632, c1803, c2, c264, c1794, c13, c1805, c1565, c106, c1769, c14, c1809, c1386, c1810, c1770] c1811 unsat1811 (by rfl) a
  have h0 : Entails.eval a c1738 := derived1738 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c1803 := derived1803 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c1794 := derived1794 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c1805 := derived1805 a h
  have h8 : Entails.eval a c1565 := derived1565 a h
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c1769 := derived1769 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c1809 := derived1809 a h
  have h13 : Entails.eval a c1386 := derived1386 a h
  have h14 : Entails.eval a c1810 := derived1810 a h
  have h15 : Entails.eval a c1770 := derived1770 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1812 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨22, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1803, some c819, some c1794, some c1811, some c107, some c15, some c1147, some c198, some c1780, some c119, some c927, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1812 : lratChecker f1812 p1812 = .success := by decide +kernel
theorem unsat1812 : Unsatisfiable (PosFin 57) f1812 := by
  apply lratCheckerSound f1812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1812
  · intro a ha; simp [p1812] at ha; subst a; trivial
  · exact checked1812
theorem derived1812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1812 := by
  apply localUnsat_implies_entails f1812 [c1803, c819, c1794, c1811, c107, c15, c1147, c198, c1780, c119, c927] c1812 unsat1812 (by rfl) a
  have h0 : Entails.eval a c1803 := derived1803 a h
  have h1 : Entails.eval a c819 := derived819 a h
  have h2 : Entails.eval a c1794 := derived1794 a h
  have h3 : Entails.eval a c1811 := derived1811 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c1780 := derived1780 a h
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c927 := derived927 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1813 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1794, some c1811, some c107, some c15, some c1632, some c1803, some c2, some c266, some c1147, some c198, some c1738, some c1812, some c263, some c771, some c849, some c170, some c139, some c79, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1813 : lratChecker f1813 p1813 = .success := by decide +kernel
theorem unsat1813 : Unsatisfiable (PosFin 57) f1813 := by
  apply lratCheckerSound f1813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1813
  · intro a ha; simp [p1813] at ha; subst a; trivial
  · exact checked1813
theorem derived1813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1813 := by
  apply localUnsat_implies_entails f1813 [c1794, c1811, c107, c15, c1632, c1803, c2, c266, c1147, c198, c1738, c1812, c263, c771, c849, c170, c139, c79] c1813 unsat1813 (by rfl) a
  have h0 : Entails.eval a c1794 := derived1794 a h
  have h1 : Entails.eval a c1811 := derived1811 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c1632 := derived1632 a h
  have h5 : Entails.eval a c1803 := derived1803 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c1738 := derived1738 a h
  have h11 : Entails.eval a c1812 := derived1812 a h
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c771 := derived771 a h
  have h14 : Entails.eval a c849 := derived849 a h
  have h15 : Entails.eval a c170 := h 169 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1813

end CochromaticTwenty.Certificates.B16_0_2Enumerating
