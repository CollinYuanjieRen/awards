import MerLeanExperiment.Certificates.B16_1_0.Steps0400_0499

/-! Generated from the actual pinned b16_1_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c897 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c791, some c892, some c204, some c884, some c198, some c894, some c9, some c1, some c895, some c205, some c18, some c881, some c120, some c896, some c209, some c74, some c72, some c167, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c791, c892, c204, c884, c198, c894, c9, c1, c895, c205, c18, c881, c120, c896, c209, c74, c72, c167] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c791 := derived791 a h
  have h1 : Entails.eval a c892 := derived892 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c884 := derived884 a h
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c894 := derived894 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c895 := derived895 a h
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c881 := derived881 a h
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c896 := derived896 a h
  have h14 : Entails.eval a c209 := h 208 (by decide)
  have h15 : Entails.eval a c74 := h 73 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c791, some c892, some c205, some c204, some c881, some c872, some c667, some c884, some c198, some c894, some c9, some c18, some c1, some c895, some c897, some c29, some c896, some c761, some c122, some c108, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c791, c892, c205, c204, c881, c872, c667, c884, c198, c894, c9, c18, c1, c895, c897, c29, c896, c761, c122, c108] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c791 := derived791 a h
  have h1 : Entails.eval a c892 := derived892 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c881 := derived881 a h
  have h5 : Entails.eval a c872 := derived872 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c884 := derived884 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c894 := derived894 a h
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c895 := derived895 a h
  have h14 : Entails.eval a c897 := derived897 a h
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c896 := derived896 a h
  have h17 : Entails.eval a c761 := derived761 a h
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨22, by decide⟩, false), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨49, by decide⟩, true), (⟨48, by decide⟩, true), (⟨24, by decide⟩, true), (⟨53, by decide⟩, true), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c239, some c296, some c267, some c221, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c366, c239, c296, c267, c221] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c791, some c892, some c881, some c29, some c130, some c872, some c667, some c57, some c327, some c318, some c104, some c88, some c14, some c392, some c394, some c256, some c301, some c818, some c763, some c111, some c388, some c255, some c122, some c31, some c39, some c51, some c899, some c379, some c381, some c372, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c791, c892, c881, c29, c130, c872, c667, c57, c327, c318, c104, c88, c14, c392, c394, c256, c301, c818, c763, c111, c388, c255, c122, c31, c39, c51, c899, c379, c381, c372] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c791 := derived791 a h
  have h1 : Entails.eval a c892 := derived892 a h
  have h2 : Entails.eval a c881 := derived881 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c872 := derived872 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c392 := h 391 (by decide)
  have h14 : Entails.eval a c394 := h 393 (by decide)
  have h15 : Entails.eval a c256 := h 255 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c818 := derived818 a h
  have h18 : Entails.eval a c763 := derived763 a h
  have h19 : Entails.eval a c111 := h 110 (by decide)
  have h20 : Entails.eval a c388 := h 387 (by decide)
  have h21 : Entails.eval a c255 := h 254 (by decide)
  have h22 : Entails.eval a c122 := h 121 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c39 := h 38 (by decide)
  have h25 : Entails.eval a c51 := h 50 (by decide)
  have h26 : Entails.eval a c899 := derived899 a h
  have h27 : Entails.eval a c379 := h 378 (by decide)
  have h28 : Entails.eval a c381 := h 380 (by decide)
  have h29 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c898, some c791, some c892, some c205, some c204, some c881, some c667, some c29, some c130, some c900, some c115, some c121, some c867, some c25, some c18, some c734, some c123, some c256, some c45, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c898, c791, c892, c205, c204, c881, c667, c29, c130, c900, c115, c121, c867, c25, c18, c734, c123, c256, c45] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c898 := derived898 a h
  have h1 : Entails.eval a c791 := derived791 a h
  have h2 : Entails.eval a c892 := derived892 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c881 := derived881 a h
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c900 := derived900 a h
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c867 := derived867 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c734 := derived734 a h
  have h16 : Entails.eval a c123 := h 122 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c901, some c791, some c892, some c204, some c205, some c898, some c118, some c25, some c119, some c113, some c18, some c130, some c123, some c44, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c901, c791, c892, c204, c205, c898, c118, c25, c119, c113, c18, c130, c123, c44] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c901 := derived901 a h
  have h1 : Entails.eval a c791 := derived791 a h
  have h2 : Entails.eval a c892 := derived892 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c898 := derived898 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c791, some c881, some c892, some c204, some c205, some c898, some c901, some c113, some c118, some c766, some c25, some c902, some c209, some c72, some c71, some c163, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c791, c881, c892, c204, c205, c898, c901, c113, c118, c766, c25, c902, c209, c72, c71, c163] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c791 := derived791 a h
  have h1 : Entails.eval a c881 := derived881 a h
  have h2 : Entails.eval a c892 := derived892 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c898 := derived898 a h
  have h6 : Entails.eval a c901 := derived901 a h
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c766 := derived766 a h
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c902 := derived902 a h
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c204, some c205, some c177, some c16, some c37, some c840, some c118, some c326, some c209, some c74, some c167, some c72, some c357, some c21, some c160, some c198, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c903, c204, c205, c177, c16, c37, c840, c118, c326, c209, c74, c167, c72, c357, c21, c160, c198] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c840 := derived840 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c167 := h 166 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c4, some c313, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c12, c4, c313] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c13, some c199, some c905, some c198, some c396, some c393, some c313, some c143, some c350, some c716, some c202, some c15, some c197, some c78, some c146, some c298, some c376, some c369, some c178, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c903, c13, c199, c905, c198, c396, c393, c313, c143, c350, c716, c202, c15, c197, c78, c146, c298, c376, c369, c178] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c905 := derived905 a h
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c396 := h 395 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c716 := derived716 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c376 := h 375 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c383, some c384, some c374, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c903, c383, c384, c374] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c384 := h 383 (by decide)
  have h3 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c904, some c198, some c199, some c22, some c906, some c195, some c191, some c907, some c37, some c118, some c113, some c90, some c103, some c389, some c387, some c368, some c194, some c186, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c903, c904, c198, c199, c22, c906, c195, c191, c907, c37, c118, c113, c90, c103, c389, c387, c368, c194, c186] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c906 := derived906 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c907 := derived907 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c387 := h 386 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  have h17 : Entails.eval a c194 := h 193 (by decide)
  have h18 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c904, some c908, some c17, some c13, some c907, some c37, some c113, some c114, some c401, some c22, some c12, some c86, some c203, some c296, some c386, some c188, some c31, some c241, some c389, some c387, some c135, some c109, some c369, some c117, some c530, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c903, c904, c908, c17, c13, c907, c37, c113, c114, c401, c22, c12, c86, c203, c296, c386, c188, c31, c241, c389, c387, c135, c109, c369, c117, c530] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c908 := derived908 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c907 := derived907 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c401 := derived401 a h
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c386 := h 385 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c241 := h 240 (by decide)
  have h19 : Entails.eval a c389 := h 388 (by decide)
  have h20 : Entails.eval a c387 := h 386 (by decide)
  have h21 : Entails.eval a c135 := h 134 (by decide)
  have h22 : Entails.eval a c109 := h 108 (by decide)
  have h23 : Entails.eval a c369 := h 368 (by decide)
  have h24 : Entails.eval a c117 := h 116 (by decide)
  have h25 : Entails.eval a c530 := derived530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c904, some c13, some c909, some c313, some c393, some c396, some c908, some c17, some c37, some c369, some c113, some c114, some c298, some c22, some c4, some c31, some c59, some c203, some c197, some c135, some c219, some c319, some c640, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c903, c904, c13, c909, c313, c393, c396, c908, c17, c37, c369, c113, c114, c298, c22, c4, c31, c59, c203, c197, c135, c219, c319, c640] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c909 := derived909 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c393 := h 392 (by decide)
  have h6 : Entails.eval a c396 := h 395 (by decide)
  have h7 : Entails.eval a c908 := derived908 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c203 := h 202 (by decide)
  have h19 : Entails.eval a c197 := h 196 (by decide)
  have h20 : Entails.eval a c135 := h 134 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  have h22 : Entails.eval a c319 := h 318 (by decide)
  have h23 : Entails.eval a c640 := derived640 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c904, some c908, some c17, some c910, some c292, some c29, some c209, some c334, some c66, some c159, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c904, c908, c17, c910, c292, c29, c209, c334, c66, c159] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c904 := derived904 a h
  have h1 : Entails.eval a c908 := derived908 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c910 := derived910 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c334 := h 333 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c292, some c29, some c209, some c334, some c66, some c159, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c292, c29, c209, c334, c66, c159] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c292 := h 291 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c334 := h 333 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c113, some c22, some c209, some c66, some c159, some c140, some c363, some c362, some c160, some c206, some c133, some c26, some c150, some c228, some c235, some c117, some c323, some c268, some c34, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c17, c113, c22, c209, c66, c159, c140, c363, c362, c160, c206, c133, c26, c150, c228, c235, c117, c323, c268, c34] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c362 := h 361 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c40, some c911, some c17, some c912, some c37, some c113, some c114, some c22, some c49, some c913, some c325, some c59, some c319, some c640, some c140, some c206, some c66, some c26, some c161, some c69, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c32, c40, c911, c17, c912, c37, c113, c114, c22, c49, c913, c325, c59, c319, c640, c140, c206, c66, c26, c161, c69] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c912 := derived912 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c913 := derived913 a h
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c640 := derived640 a h
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c66 := h 65 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c113, some c114, some c22, some c905, some c200, some c201, some c26, some c117, some c7, some c15, some c315, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c13, c113, c114, c22, c905, c200, c201, c26, c117, c7, c15, c315] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c905 := derived905 a h
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c110, some c63, some c313, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c903, c110, c63, c313] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨32, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c857, some c151, some c219, some c127, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c855, c857, c151, c219, c127] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c857 := derived857 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c32, some c914, some c915, some c44, some c13, some c40, some c911, some c200, some c124, some c26, some c49, some c121, some c16, some c90, some c299, some c180, some c35, some c717, some c340, some c916, some c917, some c282, some c72, some c337, some c365, some c242, some c230, some c268, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c903, c32, c914, c915, c44, c13, c40, c911, c200, c124, c26, c49, c121, c16, c90, c299, c180, c35, c717, c340, c916, c917, c282, c72, c337, c365, c242, c230, c268] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c914 := derived914 a h
  have h3 : Entails.eval a c915 := derived915 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c911 := derived911 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c299 := h 298 (by decide)
  have h16 : Entails.eval a c180 := h 179 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c717 := derived717 a h
  have h19 : Entails.eval a c340 := h 339 (by decide)
  have h20 : Entails.eval a c916 := derived916 a h
  have h21 : Entails.eval a c917 := derived917 a h
  have h22 : Entails.eval a c282 := h 281 (by decide)
  have h23 : Entails.eval a c72 := h 71 (by decide)
  have h24 : Entails.eval a c337 := h 336 (by decide)
  have h25 : Entails.eval a c365 := h 364 (by decide)
  have h26 : Entails.eval a c242 := h 241 (by decide)
  have h27 : Entails.eval a c230 := h 229 (by decide)
  have h28 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c914, some c13, some c32, some c40, some c911, some c915, some c44, some c918, some c22, some c118, some c16, some c90, some c299, some c35, some c916, some c917, some c717, some c340, some c282, some c72, some c365, some c162, some c230, some c127, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c903, c914, c13, c32, c40, c911, c915, c44, c918, c22, c118, c16, c90, c299, c35, c916, c917, c717, c340, c282, c72, c365, c162, c230, c127] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c914 := derived914 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c911 := derived911 a h
  have h6 : Entails.eval a c915 := derived915 a h
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c918 := derived918 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c916 := derived916 a h
  have h16 : Entails.eval a c917 := derived917 a h
  have h17 : Entails.eval a c717 := derived717 a h
  have h18 : Entails.eval a c340 := h 339 (by decide)
  have h19 : Entails.eval a c282 := h 281 (by decide)
  have h20 : Entails.eval a c72 := h 71 (by decide)
  have h21 : Entails.eval a c365 := h 364 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c230 := h 229 (by decide)
  have h24 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c40, some c911, some c13, some c919, some c10, some c29, some c309, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c32, c40, c911, c13, c919, c10, c29, c309] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c919 := derived919 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c29, some c37, some c292, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c29, c37, c292] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨53, by decide⟩, false), (⟨26, by decide⟩, false), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c325, some c326, some c156, some c207, some c158, some c190, some c315, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c309, c325, c326, c156, c207, c158, c190, c315] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c190, some c315, some c396, some c146, some c7, some c566, some c374, some c78, some c181, some c143, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c903, c190, c315, c396, c146, c7, c566, c374, c78, c181, c143] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c396 := h 395 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c566 := derived566 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c181 := h 180 (by decide)
  have h10 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c325, some c40, some c292, some c921, some c920, some c911, some c309, some c922, some c184, some c923, some c207, some c183, some c905, some c241, some c369, some c114, some c44, some c253, some c127, some c9, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c32, c325, c40, c292, c921, c920, c911, c309, c922, c184, c923, c207, c183, c905, c241, c369, c114, c44, c253, c127, c9] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c292 := h 291 (by decide)
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c920 := derived920 a h
  have h6 : Entails.eval a c911 := derived911 a h
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c922 := derived922 a h
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c923 := derived923 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c905 := derived905 a h
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c924, some c32, some c325, some c40, some c292, some c921, some c920, some c207, some c183, some c4, some c241, some c369, some c114, some c44, some c102, some c253, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c924, c32, c325, c40, c292, c921, c920, c207, c183, c4, c241, c369, c114, c44, c102, c253] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c924 := derived924 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c921 := derived921 a h
  have h6 : Entails.eval a c920 := derived920 a h
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c49, some c44, some c102, some c250, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c107, c49, c44, c102, c250] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c32, some c40, some c911, some c925, some c190, some c924, some c325, some c292, some c921, some c920, some c90, some c118, some c49, some c107, some c926, some c114, some c566, some c4, some c390, some c181, some c367, some c95, some c379, some c577, some c240, some c257, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c903, c32, c40, c911, c925, c190, c924, c325, c292, c921, c920, c90, c118, c49, c107, c926, c114, c566, c4, c390, c181, c367, c95, c379, c577, c240, c257] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c911 := derived911 a h
  have h4 : Entails.eval a c925 := derived925 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c924 := derived924 a h
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c921 := derived921 a h
  have h10 : Entails.eval a c920 := derived920 a h
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c926 := derived926 a h
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c566 := derived566 a h
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c390 := h 389 (by decide)
  have h20 : Entails.eval a c181 := h 180 (by decide)
  have h21 : Entails.eval a c367 := h 366 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  have h23 : Entails.eval a c379 := h 378 (by decide)
  have h24 : Entails.eval a c577 := derived577 a h
  have h25 : Entails.eval a c240 := h 239 (by decide)
  have h26 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c924, some c32, some c325, some c40, some c292, some c326, some c921, some c920, some c911, some c925, some c190, some c927, some c184, some c16, some c158, some c118, some c298, some c926, some c241, some c114, some c566, some c31, some c260, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c903, c924, c32, c325, c40, c292, c326, c921, c920, c911, c925, c190, c927, c184, c16, c158, c118, c298, c926, c241, c114, c566, c31, c260] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c924 := derived924 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c325 := h 324 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c920 := derived920 a h
  have h9 : Entails.eval a c911 := derived911 a h
  have h10 : Entails.eval a c925 := derived925 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c927 := derived927 a h
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c298 := h 297 (by decide)
  have h18 : Entails.eval a c926 := derived926 a h
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c114 := h 113 (by decide)
  have h21 : Entails.eval a c566 := derived566 a h
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c325, some c326, some c865, some c113, some c107, some c59, some c307, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c32, c325, c326, c865, c113, c107, c59, c307] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c865 := derived865 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c40, some c921, some c920, some c326, some c924, some c928, some c929, some c114, some c102, some c926, some c302, some c118, some c56, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c32, c40, c921, c920, c326, c924, c928, c929, c114, c102, c926, c302, c118, c56] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c920 := derived920 a h
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c924 := derived924 a h
  have h6 : Entails.eval a c928 := derived928 a h
  have h7 : Entails.eval a c929 := derived929 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c926 := derived926 a h
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c16, some c90, some c184, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c903, c16, c90, c184] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c299, some c860, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c184, c299, c860] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c860 := derived860 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨26, by decide⟩, true), (⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c298, some c151, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c183, c298, c151] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c376, some c921, some c931, some c118, some c566, some c390, some c367, some c509, some c241, some c260, some c31, some c39, some c296, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c903, c376, c921, c931, c118, c566, c390, c367, c509, c241, c260, c31, c39, c296] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c566 := derived566 a h
  have h6 : Entails.eval a c390 := h 389 (by decide)
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c509 := derived509 a h
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c32, some c40, some c911, some c920, some c921, some c930, some c209, some c931, some c118, some c932, some c933, some c376, some c934, some c114, some c72, some c926, some c315, some c396, some c151, some c374, some c207, some c296, some c143, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c903, c32, c40, c911, c920, c921, c930, c209, c931, c118, c932, c933, c376, c934, c114, c72, c926, c315, c396, c151, c374, c207, c296, c143] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c911 := derived911 a h
  have h4 : Entails.eval a c920 := derived920 a h
  have h5 : Entails.eval a c921 := derived921 a h
  have h6 : Entails.eval a c930 := derived930 a h
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c931 := derived931 a h
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c932 := derived932 a h
  have h11 : Entails.eval a c933 := derived933 a h
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c934 := derived934 a h
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c926 := derived926 a h
  have h17 : Entails.eval a c315 := h 314 (by decide)
  have h18 : Entails.eval a c396 := h 395 (by decide)
  have h19 : Entails.eval a c151 := h 150 (by decide)
  have h20 : Entails.eval a c374 := h 373 (by decide)
  have h21 : Entails.eval a c207 := h 206 (by decide)
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c509, some c97, some c122, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c377, c509, c97, c122] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c509 := derived509 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨55, by decide⟩, false), (⟨17, by decide⟩, false), (⟨50, by decide⟩, false), (⟨8, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c120, some c37, some c384, some c907, some c388, some c367, some c377, some c383, some c936, some c121, some c46, some c486, some c267, some c242, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c903, c120, c37, c384, c907, c388, c367, c377, c383, c936, c121, c46, c486, c267, c242] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c907 := derived907 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c367 := h 366 (by decide)
  have h7 : Entails.eval a c377 := h 376 (by decide)
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c936 := derived936 a h
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c486 := derived486 a h
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨34, by decide⟩, true), (⟨37, by decide⟩, false), (⟨10, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c339, some c162, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c183, c339, c162] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c935, some c931, some c120, some c29, some c37, some c555, some c921, some c177, some c384, some c907, some c388, some c212, some c367, some c334, some c285, some c216, some c938, some c376, some c937, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c903, c935, c931, c120, c29, c37, c555, c921, c177, c384, c907, c388, c212, c367, c334, c285, c216, c938, c376, c937] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c935 := derived935 a h
  have h2 : Entails.eval a c931 := derived931 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c555 := derived555 a h
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c907 := derived907 a h
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  have h16 : Entails.eval a c216 := h 215 (by decide)
  have h17 : Entails.eval a c938 := derived938 a h
  have h18 : Entails.eval a c376 := h 375 (by decide)
  have h19 : Entails.eval a c937 := derived937 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨17, by decide⟩, false), (⟨8, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c935, some c120, some c377, some c936, some c243, some c121, some c267, some c46, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c935, c120, c377, c936, c243, c121, c267, c46] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c221, some c243, some c290, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c221, c243, c290] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c221 := h 220 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, true), (⟨17, by decide⟩, false), (⟨50, by decide⟩, false), (⟨19, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c29, some c290, some c382, some c3, some c367, some c175, some c124, some c602, some c250, some c388, some c253, some c1, some c106, some c47, some c116, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c903, c29, c290, c382, c3, c367, c175, c124, c602, c250, c388, c253, c1, c106, c47, c116] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c602 := derived602 a h
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c253 := h 252 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨50, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c935, some c120, some c940, some c267, some c46, some c121, some c942, some c484, some c85, some c83, some c250, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c935, c120, c940, c267, c46, c121, c942, c484, c85, c83, c250] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c940 := derived940 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c942 := derived942 a h
  have h7 : Entails.eval a c484 := derived484 a h
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c238, some c285, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c216, c238, c285] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c238 := h 237 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨55, by decide⟩, false), (⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c212, some c939, some c935, some c120, some c80, some c29, some c941, some c944, some c940, some c943, some c10, some c204, some c205, some c147, some c195, some c293, some c390, some c367, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c903, c212, c939, c935, c120, c80, c29, c941, c944, c940, c943, c10, c204, c205, c147, c195, c293, c390, c367] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c939 := derived939 a h
  have h3 : Entails.eval a c935 := derived935 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c941 := derived941 a h
  have h8 : Entails.eval a c944 := derived944 a h
  have h9 : Entails.eval a c940 := derived940 a h
  have h10 : Entails.eval a c943 := derived943 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c293 := h 292 (by decide)
  have h17 : Entails.eval a c390 := h 389 (by decide)
  have h18 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c90, some c382, some c787, some c46, some c484, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c903, c90, c382, c787, c46, c484] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c787 := derived787 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c484 := derived484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c90, some c212, some c935, some c225, some c247, some c301, some c946, some c119, some c73, some c63, some c209, some c291, some c855, some c550, some c113, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c903, c90, c212, c935, c225, c247, c301, c946, c119, c73, c63, c209, c291, c855, c550, c113] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c935 := derived935 a h
  have h4 : Entails.eval a c225 := h 224 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c301 := h 300 (by decide)
  have h7 : Entails.eval a c946 := derived946 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c209 := h 208 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c855 := derived855 a h
  have h14 : Entails.eval a c550 := derived550 a h
  have h15 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c939, some c935, some c16, some c90, some c205, some c382, some c243, some c947, some c267, some c273, some c238, some c944, some c45, some c936, some c29, some c113, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c903, c939, c935, c16, c90, c205, c382, c243, c947, c267, c273, c238, c944, c45, c936, c29, c113] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c939 := derived939 a h
  have h2 : Entails.eval a c935 := derived935 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c243 := h 242 (by decide)
  have h8 : Entails.eval a c947 := derived947 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c273 := h 272 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c944 := derived944 a h
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c936 := derived936 a h
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c939, some c935, some c948, some c120, some c945, some c29, some c376, some c941, some c944, some c382, some c940, some c267, some c372, some c46, some c250, some c484, some c83, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c903, c939, c935, c948, c120, c945, c29, c376, c941, c944, c382, c940, c267, c372, c46, c250, c484, c83] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c939 := derived939 a h
  have h2 : Entails.eval a c935 := derived935 a h
  have h3 : Entails.eval a c948 := derived948 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c945 := derived945 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c941 := derived941 a h
  have h9 : Entails.eval a c944 := derived944 a h
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c940 := derived940 a h
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c372 := h 371 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c484 := derived484 a h
  have h17 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c376, some c89, some c382, some c117, some c372, some c83, some c250, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c903, c376, c89, c382, c117, c372, c83, c250] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c205, some c156, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c204, c205, c156] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c267, some c46, some c946, some c943, some c940, some c950, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c10, c267, c46, c946, c943, c940, c950] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c946 := derived946 a h
  have h4 : Entails.eval a c943 := derived943 a h
  have h5 : Entails.eval a c940 := derived940 a h
  have h6 : Entails.eval a c950 := derived950 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c949, some c939, some c29, some c326, some c325, some c951, some c10, some c309, some c952, some c243, some c290, some c377, some c382, some c30, some c220, some c366, some c90, some c376, some c268, some c388, some c391, some c121, some c47, some c613, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c903, c949, c939, c29, c326, c325, c951, c10, c309, c952, c243, c290, c377, c382, c30, c220, c366, c90, c376, c268, c388, c391, c121, c47, c613] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c939 := derived939 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c951 := derived951 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c952 := derived952 a h
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c376 := h 375 (by decide)
  have h19 : Entails.eval a c268 := h 267 (by decide)
  have h20 : Entails.eval a c388 := h 387 (by decide)
  have h21 : Entails.eval a c391 := h 390 (by decide)
  have h22 : Entails.eval a c121 := h 120 (by decide)
  have h23 : Entails.eval a c47 := h 46 (by decide)
  have h24 : Entails.eval a c613 := derived613 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c325, some c63, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c326, c325, c63] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c949, some c939, some c935, some c953, some c120, some c119, some c16, some c90, some c205, some c382, some c243, some c267, some c247, some c186, some c954, some c209, some c218, some c73, some c335, some c301, some c236, some c63, some c328, some c151, some c65, some c284, some c207, some c81, some c24, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c903, c949, c939, c935, c953, c120, c119, c16, c90, c205, c382, c243, c267, c247, c186, c954, c209, c218, c73, c335, c301, c236, c63, c328, c151, c65, c284, c207, c81, c24] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c949 := derived949 a h
  have h2 : Entails.eval a c939 := derived939 a h
  have h3 : Entails.eval a c935 := derived935 a h
  have h4 : Entails.eval a c953 := derived953 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c382 := h 381 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c247 := h 246 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c954 := derived954 a h
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c73 := h 72 (by decide)
  have h19 : Entails.eval a c335 := h 334 (by decide)
  have h20 : Entails.eval a c301 := h 300 (by decide)
  have h21 : Entails.eval a c236 := h 235 (by decide)
  have h22 : Entails.eval a c63 := h 62 (by decide)
  have h23 : Entails.eval a c328 := h 327 (by decide)
  have h24 : Entails.eval a c151 := h 150 (by decide)
  have h25 : Entails.eval a c65 := h 64 (by decide)
  have h26 : Entails.eval a c284 := h 283 (by decide)
  have h27 : Entails.eval a c207 := h 206 (by decide)
  have h28 : Entails.eval a c81 := h 80 (by decide)
  have h29 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c120, some c119, some c113, some c16, some c110, some c28, some c103, some c205, some c388, some c390, some c895, some c190, some c207, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c903, c120, c119, c113, c16, c110, c28, c103, c205, c388, c390, c895, c190, c207] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c390 := h 389 (by decide)
  have h11 : Entails.eval a c895 := derived895 a h
  have h12 : Entails.eval a c190 := h 189 (by decide)
  have h13 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c939, some c935, some c949, some c955, some c238, some c377, some c936, some c243, some c956, some c29, some c326, some c285, some c28, some c217, some c796, some c273, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c939, c935, c949, c955, c238, c377, c936, c243, c956, c29, c326, c285, c28, c217, c796, c273] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c935 := derived935 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c955 := derived955 a h
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c936 := derived936 a h
  have h7 : Entails.eval a c243 := h 242 (by decide)
  have h8 : Entails.eval a c956 := derived956 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c796 := derived796 a h
  have h15 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c935, some c119, some c120, some c216, some c208, some c954, some c66, some c209, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c935, c119, c120, c216, c208, c954, c66, c209] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c954 := derived954 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c66, some c227, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c73, c66, c227] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c935, some c119, some c958, some c959, some c209, some c319, some c320, some c59, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c935, c119, c958, c959, c209, c319, c320, c59] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c958 := derived958 a h
  have h3 : Entails.eval a c959 := derived959 a h
  have h4 : Entails.eval a c209 := h 208 (by decide)
  have h5 : Entails.eval a c319 := h 318 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c390, some c369, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c388, c390, c369] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c935, some c957, some c37, some c241, some c120, some c119, some c90, some c110, some c961, some c103, some c113, some c960, some c499, some c268, some c269, some c385, some c51, some c484, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c903, c935, c957, c37, c241, c120, c119, c90, c110, c961, c103, c113, c960, c499, c268, c269, c385, c51, c484] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c935 := derived935 a h
  have h2 : Entails.eval a c957 := derived957 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c961 := derived961 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c960 := derived960 a h
  have h13 : Entails.eval a c499 := derived499 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c484 := derived484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨49, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨47, by decide⟩, false), (⟨45, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c16, some c205, some c110, some c90, some c243, some c95, some c267, some c380, some c247, some c366, some c186, some c396, some c393, some c112, some c190, some c117, some c207, some c24, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c903, c16, c205, c110, c90, c243, c95, c267, c380, c247, c366, c186, c396, c393, c112, c190, c117, c207, c24] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  have h12 : Entails.eval a c396 := h 395 (by decide)
  have h13 : Entails.eval a c393 := h 392 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c207 := h 206 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c90, some c16, some c385, some c180, some c247, some c11, some c3, some c267, some c269, some c295, some c50, some c35, some c117, some c139, some c14, some c6, some c311, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c903, c90, c16, c385, c180, c247, c11, c3, c267, c269, c295, c50, c35, c117, c139, c14, c6, c311] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c269 := h 268 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c935, some c119, some c120, some c962, some c939, some c113, some c960, some c964, some c243, some c85, some c963, some c250, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c935, c119, c120, c962, c939, c113, c960, c964, c243, c85, c963, c250] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c962 := derived962 a h
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c960 := derived960 a h
  have h7 : Entails.eval a c964 := derived964 a h
  have h8 : Entails.eval a c243 := h 242 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c963 := derived963 a h
  have h11 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c962, some c939, some c935, some c120, some c119, some c16, some c90, some c110, some c205, some c965, some c103, some c388, some c390, some c112, some c190, some c207, some c4, some c895, some c28, some c56, some c1, some c251, some c127, some c202, some c838, some c39, some c24, some c252, some c297, some c247, some c214, some c301, some c81, some c213, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 57) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c903, c962, c939, c935, c120, c119, c16, c90, c110, c205, c965, c103, c388, c390, c112, c190, c207, c4, c895, c28, c56, c1, c251, c127, c202, c838, c39, c24, c252, c297, c247, c214, c301, c81, c213] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c962 := derived962 a h
  have h2 : Entails.eval a c939 := derived939 a h
  have h3 : Entails.eval a c935 := derived935 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c965 := derived965 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c390 := h 389 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c190 := h 189 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c895 := derived895 a h
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c56 := h 55 (by decide)
  have h21 : Entails.eval a c1 := h 0 (by decide)
  have h22 : Entails.eval a c251 := h 250 (by decide)
  have h23 : Entails.eval a c127 := h 126 (by decide)
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c838 := derived838 a h
  have h26 : Entails.eval a c39 := h 38 (by decide)
  have h27 : Entails.eval a c24 := h 23 (by decide)
  have h28 : Entails.eval a c252 := h 251 (by decide)
  have h29 : Entails.eval a c297 := h 296 (by decide)
  have h30 : Entails.eval a c247 := h 246 (by decide)
  have h31 : Entails.eval a c214 := h 213 (by decide)
  have h32 : Entails.eval a c301 := h 300 (by decide)
  have h33 : Entails.eval a c81 := h 80 (by decide)
  have h34 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c16, some c103, some c110, some c205, some c388, some c10, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 57) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c903, c16, c103, c110, c205, c388, c10] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c968 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c871, some c387, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 57) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c10, c871, c387] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c871 := derived871 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c967, some c968, some c204, some c4, some c12, some c895, some c291, some c28, some c39, some c251, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 57) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c967, c968, c204, c4, c12, c895, c291, c28, c39, c251] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c967 := derived967 a h
  have h1 : Entails.eval a c968 := derived968 a h
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c895 := derived895 a h
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c967, some c969, some c83, some c378, some c509, some c381, some c121, some c98, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 57) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c967, c969, c83, c378, c509, c381, c121, c98] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c967 := derived967 a h
  have h1 : Entails.eval a c969 := derived969 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c509 := derived509 a h
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c971 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c83, some c9, some c170, some c174, some c20, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 57) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c83, c9, c170, c174, c20] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c170 := h 169 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c972 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨45, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c381, some c285, some c243, some c247, some c28, some c267, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 57) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c377, c381, c285, c243, c247, c28, c267] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  have h3 : Entails.eval a c243 := h 242 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c966, some c37, some c29, some c962, some c939, some c935, some c970, some c122, some c47, some c971, some c972, some c36, some c269, some c253, some c46, some c734, some c387, some c108, some c112, some c121, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 57) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c903, c966, c37, c29, c962, c939, c935, c970, c122, c47, c971, c972, c36, c269, c253, c46, c734, c387, c108, c112, c121] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c966 := derived966 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c962 := derived962 a h
  have h5 : Entails.eval a c939 := derived939 a h
  have h6 : Entails.eval a c935 := derived935 a h
  have h7 : Entails.eval a c970 := derived970 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c971 := derived971 a h
  have h11 : Entails.eval a c972 := derived972 a h
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c253 := h 252 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c734 := derived734 a h
  have h17 : Entails.eval a c387 := h 386 (by decide)
  have h18 : Entails.eval a c108 := h 107 (by decide)
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c734, some c108, some c387, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 57) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c253, c734, c108, c387] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c734 := derived734 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨22, by decide⟩, true), (⟨26, by decide⟩, false), (⟨47, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c307, some c225, some c61, some c300, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 57) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c309, c307, c225, c61, c300] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c307 := h 306 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, true), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨47, by decide⟩, false), (⟨45, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c247, some c238, some c974, some c366, some c367, some c382, some c85, some c975, some c734, some c10, some c396, some c204, some c205, some c195, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 57) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c903, c247, c238, c974, c366, c367, c382, c85, c975, c734, c10, c396, c204, c205, c195] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c974 := derived974 a h
  have h4 : Entails.eval a c366 := h 365 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c975 := derived975 a h
  have h9 : Entails.eval a c734 := derived734 a h
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c396 := h 395 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨41, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c939, some c238, some c973, some c966, some c37, some c29, some c962, some c935, some c46, some c796, some c117, some c47, some c268, some c976, some c31, some c39, some c291, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 57) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c939, c238, c973, c966, c37, c29, c962, c935, c46, c796, c117, c47, c268, c976, c31, c39, c291] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c238 := h 237 (by decide)
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c966 := derived966 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c962 := derived962 a h
  have h7 : Entails.eval a c935 := derived935 a h
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c796 := derived796 a h
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c976 := derived976 a h
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c973, some c966, some c37, some c29, some c939, some c935, some c238, some c977, some c267, some c269, some c243, some c941, some c47, some c290, some c382, some c326, some c325, some c122, some c117, some c222, some c30, some c210, some c90, some c62, some c323, some c76, some c67, some c276, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 57) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c903, c973, c966, c37, c29, c939, c935, c238, c977, c267, c269, c243, c941, c47, c290, c382, c326, c325, c122, c117, c222, c30, c210, c90, c62, c323, c76, c67, c276] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c973 := derived973 a h
  have h2 : Entails.eval a c966 := derived966 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c939 := derived939 a h
  have h6 : Entails.eval a c935 := derived935 a h
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c977 := derived977 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c941 := derived941 a h
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c326 := h 325 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c222 := h 221 (by decide)
  have h21 : Entails.eval a c30 := h 29 (by decide)
  have h22 : Entails.eval a c210 := h 209 (by decide)
  have h23 : Entails.eval a c90 := h 89 (by decide)
  have h24 : Entails.eval a c62 := h 61 (by decide)
  have h25 : Entails.eval a c323 := h 322 (by decide)
  have h26 : Entails.eval a c76 := h 75 (by decide)
  have h27 : Entails.eval a c67 := h 66 (by decide)
  have h28 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c939, some c962, some c966, some c29, some c37, some c978, some c377, some c381, some c285, some c243, some c247, some c267, some c273, some c216, some c217, some c326, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 57) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c939, c962, c966, c29, c37, c978, c377, c381, c285, c243, c247, c267, c273, c216, c217, c326] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c962 := derived962 a h
  have h2 : Entails.eval a c966 := derived966 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c978 := derived978 a h
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c217 := h 216 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c273, some c216, some c217, some c326, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 57) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c267, c273, c216, c217, c326] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c217 := h 216 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c29, some c37, some c285, some c377, some c935, some c243, some c980, some c247, some c46, some c381, some c508, some c936, some c121, some c90, some c56, some c293, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 57) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c903, c29, c37, c285, c377, c935, c243, c980, c247, c46, c381, c508, c936, c121, c90, c56, c293] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c935 := derived935 a h
  have h6 : Entails.eval a c243 := h 242 (by decide)
  have h7 : Entails.eval a c980 := derived980 a h
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c381 := h 380 (by decide)
  have h11 : Entails.eval a c508 := derived508 a h
  have h12 : Entails.eval a c936 := derived936 a h
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c170, some c509, some c936, some c122, some c174, some c20, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 57) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c170, c509, c936, c122, c174, c20] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c170 := h 169 (by decide)
  have h1 : Entails.eval a c509 := derived509 a h
  have h2 : Entails.eval a c936 := derived936 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c37, some c29, some c979, some c935, some c285, some c981, some c921, some c384, some c148, some c216, some c90, some c170, some c982, some c121, some c46, some c19, some c126, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 57) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c903, c37, c29, c979, c935, c285, c981, c921, c384, c148, c216, c90, c170, c982, c121, c46, c19, c126] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c979 := derived979 a h
  have h4 : Entails.eval a c935 := derived935 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c981 := derived981 a h
  have h7 : Entails.eval a c921 := derived921 a h
  have h8 : Entails.eval a c384 := h 383 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c170 := h 169 (by decide)
  have h13 : Entails.eval a c982 := derived982 a h
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c984 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c980, some c148, some c216, some c941, some c126, some c384, some c14, some c367, some c252, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 57) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c903, c980, c148, c216, c941, c126, c384, c14, c367, c252] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c980 := derived980 a h
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c941 := derived941 a h
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c282, some c359, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 57) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c276, c282, c359] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c37, some c29, some c979, some c935, some c46, some c980, some c984, some c921, some c326, some c325, some c243, some c238, some c290, some c269, some c210, some c47, some c332, some c122, some c230, some c985, some c63, some c751, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 57) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c983, c37, c29, c979, c935, c46, c980, c984, c921, c326, c325, c243, c238, c290, c269, c210, c47, c332, c122, c230, c985, c63, c751] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c979 := derived979 a h
  have h4 : Entails.eval a c935 := derived935 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c980 := derived980 a h
  have h7 : Entails.eval a c984 := derived984 a h
  have h8 : Entails.eval a c921 := derived921 a h
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c325 := h 324 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c230 := h 229 (by decide)
  have h20 : Entails.eval a c985 := derived985 a h
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c751 := derived751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c987 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨45, by decide⟩, true), (⟨6, by decide⟩, false), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c243, some c290, some c382, some c30, some c90, some c121, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 57) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c903, c243, c290, c382, c30, c90, c121] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c59, some c124, some c122, some c149, some c47, some c133, some c268, some c224, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 57) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c3, c59, c124, c122, c149, c47, c133, c268, c224] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c29, some c37, some c986, some c921, some c987, some c983, some c238, some c325, some c326, some c979, some c935, some c988, some c290, some c85, some c250, some c307, some c367, some c10, some c178, some c640, some c156, some c199, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c903, c29, c37, c986, c921, c987, c983, c238, c325, c326, c979, c935, c988, c290, c85, c250, c307, c367, c10, c178, c640, c156, c199] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c986 := derived986 a h
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c987 := derived987 a h
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c326 := h 325 (by decide)
  have h10 : Entails.eval a c979 := derived979 a h
  have h11 : Entails.eval a c935 := derived935 a h
  have h12 : Entails.eval a c988 := derived988 a h
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c367 := h 366 (by decide)
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c640 := derived640 a h
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c986, some c29, some c326, some c989, some c121, some c115, some c56, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 57) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c986, c29, c326, c989, c121, c115, c56] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c986 := derived986 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c326 := h 325 (by decide)
  have h3 : Entails.eval a c989 := derived989 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c990, some c216, some c979, some c148, some c37, some c29, some c16, some c90, some c178, some c384, some c293, some c10, some c941, some c56, some c35, some c980, some c124, some c796, some c672, some c11, some c307, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 57) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c903, c990, c216, c979, c148, c37, c29, c16, c90, c178, c384, c293, c10, c941, c56, c35, c980, c124, c796, c672, c11, c307] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c990 := derived990 a h
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c979 := derived979 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c384 := h 383 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c941 := derived941 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c980 := derived980 a h
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c796 := derived796 a h
  have h19 : Entails.eval a c672 := derived672 a h
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c147, some c215, some c672, some c290, some c38, some c85, some c250, some c307, some c367, some c10, some c178, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 57) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c903, c147, c215, c672, c290, c38, c85, c250, c307, c367, c10, c178] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c672 := derived672 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨2, by decide⟩, true), (⟨21, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c37, some c29, some c979, some c935, some c986, some c990, some c144, some c148, some c216, some c991, some c121, some c80, some c992, some c324, some c153, some c221, some c124, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 57) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c983, c37, c29, c979, c935, c986, c990, c144, c148, c216, c991, c121, c80, c992, c324, c153, c221, c124] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c979 := derived979 a h
  have h4 : Entails.eval a c935 := derived935 a h
  have h5 : Entails.eval a c986 := derived986 a h
  have h6 : Entails.eval a c990 := derived990 a h
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c991 := derived991 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c992 := derived992 a h
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c221 := h 220 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c225, some c132, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c157, c225, c132] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c225 := h 224 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨19, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c273, some c238, some c239, some c384, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c267, c273, c238, c239, c384] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c61, some c122, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c59, c61, c122] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived996

end CochromaticTwenty.Certificates.B16_1_0
