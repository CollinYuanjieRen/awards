import MerLeanExperiment.Certificates.B16_2_2.Steps0400_0499

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c884 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨15, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c134, some c158, some c355, some c70, some c154, some c20, some c192, some c4, some c53, some c68, some c132, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c160, c134, c158, c355, c70, c154, c20, c192, c4, c53, c68, c132] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c68, some c132, some c200, some c118, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c53, c68, c132, c200, c118] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c71, some c204, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c55, c71, c204] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c381, some c101, some c111, some c99, some c35, some c245, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c380, c381, c101, c111, c99, c35, c245] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c338, some c299, some c198, some c247, some c120, some c887, some c886, some c20, some c112, some c14, some c34, some c117, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c338, c299, c198, c247, c120, c887, c886, c20, c112, c14, c34, c117] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c338 := h 337 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c247 := h 246 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c887 := derived887 a h
  have h6 : Entails.eval a c886 := derived886 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c186, some c381, some c380, some c187, some c191, some c884, some c888, some c146, some c148, some c315, some c54, some c142, some c20, some c192, some c4, some c69, some c52, some c132, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c186, c381, c380, c187, c191, c884, c888, c146, c148, c315, c54, c142, c20, c192, c4, c69, c52, c132] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c186 := h 185 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c884 := derived884 a h
  have h6 : Entails.eval a c888 := derived888 a h
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c315 := h 314 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c142 := h 141 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c769, some c185, some c192, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c769, c185, c192] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c769 := derived769 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c306, some c148, some c191, some c383, some c376, some c883, some c890, some c705, some c743, some c192, some c203, some c4, some c256, some c115, some c123, some c111, some c530, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c146, c306, c148, c191, c383, c376, c883, c890, c705, c743, c192, c203, c4, c256, c115, c123, c111, c530] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c883 := derived883 a h
  have h7 : Entails.eval a c890 := derived890 a h
  have h8 : Entails.eval a c705 := derived705 a h
  have h9 : Entails.eval a c743 := derived743 a h
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c115 := h 114 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c111 := h 110 (by decide)
  have h17 : Entails.eval a c530 := derived530 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c889, some c146, some c306, some c148, some c191, some c134, some c383, some c891, some c380, some c304, some c182, some c192, some c132, some c69, some c343, some c17, some c159, some c71, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c883, c889, c146, c306, c148, c191, c134, c383, c891, c380, c304, c182, c192, c132, c69, c343, c17, c159, c71] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c891 := derived891 a h
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  have h18 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c889, some c383, some c376, some c146, some c306, some c148, some c191, some c892, some c6, some c381, some c380, some c890, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c883, c889, c383, c376, c146, c306, c148, c191, c892, c6, c381, c380, c890] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c892 := derived892 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c381 := h 380 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c890 := derived890 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨52, by decide⟩, true), (⟨16, by decide⟩, true), (⟨51, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c185, some c192, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c183, c185, c192] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c376, some c883, some c894, some c589, some c705, some c6, some c192, some c4, some c111, some c53, some c109, some c132, some c739, some c69, some c884, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c383, c376, c883, c894, c589, c705, c6, c192, c4, c111, c53, c109, c132, c739, c69, c884] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c894 := derived894 a h
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c705 := derived705 a h
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c739 := derived739 a h
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c884 := derived884 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c156, some c135, some c343, some c306, some c133, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c156, c135, c343, c306, c133] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c156 := h 155 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨16, by decide⟩, true), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c343, some c159, some c158, some c71, some c69, some c17, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c343, c159, c158, c71, c69, c17] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c343 := h 342 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨32, by decide⟩, false), (⟨26, by decide⟩, true), (⟨40, by decide⟩, false), (⟨16, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c743, some c339, some c269, some c308, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c743, c339, c269, c308] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c743 := derived743 a h
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c899 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨30, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f899 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c883, some c895, some c380, some c182, some c6, some c192, some c897, some c132, some c304, some c53, some c147, some c17, some c55, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p899 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked899 : lratChecker f899 p899 = .success := by decide +kernel
theorem unsat899 : Unsatisfiable (PosFin 57) f899 := by
  apply lratCheckerSound f899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p899
  · intro a ha; simp [p899] at ha; subst a; trivial
  · exact checked899
theorem derived899 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c899 := by
  apply localUnsat_implies_entails f899 [c383, c883, c895, c380, c182, c6, c192, c897, c132, c304, c53, c147, c17, c55] c899 unsat899 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c895 := derived895 a h
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c897 := derived897 a h
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c900 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨15, by decide⟩, true), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f900 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c896, some c345, some c133, some c306, some c304, some c144, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p900 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked900 : lratChecker f900 p900 = .success := by decide +kernel
theorem unsat900 : Unsatisfiable (PosFin 57) f900 := by
  apply lratCheckerSound f900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p900
  · intro a ha; simp [p900] at ha; subst a; trivial
  · exact checked900
theorem derived900 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c900 := by
  apply localUnsat_implies_entails f900 [c896, c345, c133, c306, c304, c144] c900 unsat900 (by rfl) a
  have h0 : Entails.eval a c896 := derived896 a h
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c901 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f901 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c883, some c380, some c182, some c192, some c900, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p901 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked901 : lratChecker f901 p901 = .success := by decide +kernel
theorem unsat901 : Unsatisfiable (PosFin 57) f901 := by
  apply lratCheckerSound f901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p901
  · intro a ha; simp [p901] at ha; subst a; trivial
  · exact checked901
theorem derived901 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c901 := by
  apply localUnsat_implies_entails f901 [c383, c883, c380, c182, c192, c900] c901 unsat901 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c900 := derived900 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c902 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f902 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c889, some c383, some c893, some c899, some c191, some c901, some c884, some c888, some c182, some c6, some c192, some c4, some c53, some c69, some c132, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p902 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked902 : lratChecker f902 p902 = .success := by decide +kernel
theorem unsat902 : Unsatisfiable (PosFin 57) f902 := by
  apply lratCheckerSound f902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p902
  · intro a ha; simp [p902] at ha; subst a; trivial
  · exact checked902
theorem derived902 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c902 := by
  apply localUnsat_implies_entails f902 [c883, c889, c383, c893, c899, c191, c901, c884, c888, c182, c6, c192, c4, c53, c69, c132] c902 unsat902 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c889 := derived889 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c893 := derived893 a h
  have h4 : Entails.eval a c899 := derived899 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c901 := derived901 a h
  have h7 : Entails.eval a c884 := derived884 a h
  have h8 : Entails.eval a c888 := derived888 a h
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c903 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c158, some c345, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p903 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 57) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c160, c158, c345] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c148, some c306, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p904 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 57) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c146, c148, c306] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c109, some c69, some c53, some c200, some c132, some c118, some c192, some c22, some c705, some c658, some c371, some c168, some c364, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p905 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 57) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c383, c109, c69, c53, c200, c132, c118, c192, c22, c705, c658, c371, c168, c364] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c705 := derived705 a h
  have h10 : Entails.eval a c658 := derived658 a h
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c902, some c5, some c376, some c18, some c883, some c191, some c901, some c903, some c904, some c905, some c4, some c95, some c192, some c106, some c705, some c101, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p906 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 57) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c902, c5, c376, c18, c883, c191, c901, c903, c904, c905, c4, c95, c192, c106, c705, c101] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c902 := derived902 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c883 := derived883 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c901 := derived901 a h
  have h7 : Entails.eval a c903 := derived903 a h
  have h8 : Entails.eval a c904 := derived904 a h
  have h9 : Entails.eval a c905 := derived905 a h
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c705 := derived705 a h
  have h15 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c903, some c904, some c71, some c55, some c136, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p907 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 57) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c903, c904, c71, c55, c136] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c903 := derived903 a h
  have h1 : Entails.eval a c904 := derived904 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c18, some c19, some c907, some c376, some c106, some c73, some c616, some c136, some c147, some c71, some c158, some c345, some c203, some c254, some c115, some c25, some c277, some c316, some c197, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p908 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 57) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c5, c18, c19, c907, c376, c106, c73, c616, c136, c147, c71, c158, c345, c203, c254, c115, c25, c277, c316, c197] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c907 := derived907 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c616 := derived616 a h
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c345 := h 344 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c902, some c5, some c18, some c376, some c906, some c19, some c106, some c73, some c907, some c908, some c55, some c134, some c146, some c71, some c306, some c159, some c345, some c203, some c254, some c115, some c25, some c277, some c316, some c197, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p909 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 57) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c902, c5, c18, c376, c906, c19, c106, c73, c907, c908, c55, c134, c146, c71, c306, c159, c345, c203, c254, c115, c25, c277, c316, c197] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c902 := derived902 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c906 := derived906 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c907 := derived907 a h
  have h9 : Entails.eval a c908 := derived908 a h
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c134 := h 133 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c203 := h 202 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  have h19 : Entails.eval a c115 := h 114 (by decide)
  have h20 : Entails.eval a c25 := h 24 (by decide)
  have h21 : Entails.eval a c277 := h 276 (by decide)
  have h22 : Entails.eval a c316 := h 315 (by decide)
  have h23 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c909, some c883, some c376, some c383, some c1, some c178, some c192, some c179, some c380, some c6, some c106, some c897, some c19, some c151, some c899, some c58, some c134, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p910 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 57) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c909, c883, c376, c383, c1, c178, c192, c179, c380, c6, c106, c897, c19, c151, c899, c58, c134] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c909 := derived909 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c897 := derived897 a h
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c899 := derived899 a h
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c910, some c186, some c187, some c381, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p911 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 57) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c910, c186, c187, c381] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c910 := derived910 a h
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c101, some c80, some c69, some c52, some c168, some c132, some c200, some c22, some c118, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p912 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 57) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c843, c101, c80, c69, c52, c168, c132, c200, c22, c118] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c142, some c50, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p913 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 57) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c10, c142, c50] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c134, some c146, some c912, some c106, some c1, some c333, some c913, some c192, some c4, some c151, some c69, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c134, c146, c912, c106, c1, c333, c913, c192, c4, c151, c69] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c134 := h 133 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c912 := derived912 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c913 := derived913 a h
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c151 := h 150 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c139, some c53, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c4, c139, c53] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c294, some c129, some c333, some c158, some c915, some c192, some c10, some c154, some c66, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c1, c294, c129, c333, c158, c915, c192, c10, c154, c66] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c915 := derived915 a h
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c916, some c42, some c129, some c58, some c57, some c158, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c916, c42, c129, c58, c57, c158] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c916 := derived916 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨13, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c914, some c917, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c914, c917] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c914 := derived914 a h
  have h1 : Entails.eval a c917 := derived917 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨33, by decide⟩, false), (⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c338, some c333, some c349, some c198, some c179, some c120, some c247, some c118, some c26, some c225, some c523, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c380, c338, c333, c349, c198, c179, c120, c247, c118, c26, c225, c523] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c225 := h 224 (by decide)
  have h11 : Entails.eval a c523 := derived523 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨37, by decide⟩, false), (⟨38, by decide⟩, true), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c10, some c154, some c66, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c10, c154, c66] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c247, some c117, some c34, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c247, c117, c34] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c247 := h 246 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c186, some c381, some c380, some c918, some c129, some c919, some c158, some c57, some c348, some c1, some c920, some c192, some c4, some c139, some c111, some c52, some c921, some c208, some c205, some c242, some c257, some c228, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c5, c186, c381, c380, c918, c129, c919, c158, c57, c348, c1, c920, c192, c4, c139, c111, c52, c921, c208, c205, c242, c257, c228] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c918 := derived918 a h
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c919 := derived919 a h
  have h7 : Entails.eval a c158 := h 157 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c920 := derived920 a h
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c921 := derived921 a h
  have h18 : Entails.eval a c208 := h 207 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c242 := h 241 (by decide)
  have h21 : Entails.eval a c257 := h 256 (by decide)
  have h22 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c186, some c381, some c380, some c918, some c299, some c922, some c294, some c1, some c179, some c41, some c192, some c133, some c14, some c57, some c66, some c150, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c5, c186, c381, c380, c918, c299, c922, c294, c1, c179, c41, c192, c133, c14, c57, c66, c150] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c918 := derived918 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c922 := derived922 a h
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c41, some c57, some c129, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c41, c57, c129] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c134, some c924, some c1, some c913, some c333, some c192, some c4, some c151, some c68, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c134, c924, c1, c913, c333, c192, c4, c151, c68] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c134 := h 133 (by decide)
  have h1 : Entails.eval a c924 := derived924 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c913 := derived913 a h
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c151 := h 150 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c925, some c134, some c338, some c1, some c913, some c333, some c192, some c129, some c4, some c295, some c111, some c921, some c220, some c217, some c242, some c257, some c216, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c380, c925, c134, c338, c1, c913, c333, c192, c129, c4, c295, c111, c921, c220, c217, c242, c257, c216] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c925 := derived925 a h
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c913 := derived913 a h
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c129 := h 128 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c921 := derived921 a h
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c217 := h 216 (by decide)
  have h15 : Entails.eval a c242 := h 241 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c911, some c909, some c883, some c5, some c186, some c381, some c380, some c918, some c923, some c134, some c146, some c926, some c105, some c41, some c20, some c129, some c922, some c333, some c179, some c192, some c769, some c142, some c297, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c911, c909, c883, c5, c186, c381, c380, c918, c923, c134, c146, c926, c105, c41, c20, c129, c922, c333, c179, c192, c769, c142, c297] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c911 := derived911 a h
  have h1 : Entails.eval a c909 := derived909 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c918 := derived918 a h
  have h8 : Entails.eval a c923 := derived923 a h
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c926 := derived926 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c41 := h 40 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c129 := h 128 (by decide)
  have h16 : Entails.eval a c922 := derived922 a h
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c769 := derived769 a h
  have h21 : Entails.eval a c142 := h 141 (by decide)
  have h22 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c777, some c133, some c304, some c41, some c139, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c777, c133, c304, c41, c139] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c777 := derived777 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c246, some c37, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c120, c246, c37] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c909, some c927, some c376, some c1, some c883, some c383, some c178, some c192, some c179, some c380, some c6, some c106, some c911, some c306, some c304, some c132, some c337, some c343, some c158, some c69, some c929, some c220, some c252, some c254, some c212, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c909, c927, c376, c1, c883, c383, c178, c192, c179, c380, c6, c106, c911, c306, c304, c132, c337, c343, c158, c69, c929, c220, c252, c254, c212] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c909 := derived909 a h
  have h1 : Entails.eval a c927 := derived927 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c883 := derived883 a h
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c911 := derived911 a h
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c304 := h 303 (by decide)
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c343 := h 342 (by decide)
  have h18 : Entails.eval a c158 := h 157 (by decide)
  have h19 : Entails.eval a c69 := h 68 (by decide)
  have h20 : Entails.eval a c929 := derived929 a h
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c252 := h 251 (by decide)
  have h23 : Entails.eval a c254 := h 253 (by decide)
  have h24 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c909, some c911, some c927, some c376, some c383, some c1, some c178, some c192, some c179, some c380, some c6, some c106, some c928, some c930, some c133, some c758, some c343, some c39, some c132, some c120, some c298, some c208, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c883, c909, c911, c927, c376, c383, c1, c178, c192, c179, c380, c6, c106, c928, c930, c133, c758, c343, c39, c132, c120, c298, c208] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c909 := derived909 a h
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c927 := derived927 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  have h8 : Entails.eval a c192 := h 191 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c928 := derived928 a h
  have h14 : Entails.eval a c930 := derived930 a h
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c758 := derived758 a h
  have h17 : Entails.eval a c343 := h 342 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c132 := h 131 (by decide)
  have h20 : Entails.eval a c120 := h 119 (by decide)
  have h21 : Entails.eval a c298 := h 297 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c133, some c146, some c758, some c312, some c208, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c304, c133, c146, c758, c312, c208] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c758 := derived758 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨28, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c52, some c305, some c80, some c168, some c359, some c288, some c24, some c567, some c210, some c249, some c99, some c112, some c16, some c88, some c176, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c314, c52, c305, c80, c168, c359, c288, c24, c567, c210, c249, c99, c112, c16, c88, c176] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c567 := derived567 a h
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c249 := h 248 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c931, some c883, some c932, some c5, some c186, some c589, some c305, some c146, some c52, some c933, some c106, some c11, some c191, some c148, some c16, some c54, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c931, c883, c932, c5, c186, c589, c305, c146, c52, c933, c106, c11, c191, c148, c16, c54] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c932 := derived932 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c933 := derived933 a h
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨38, by decide⟩, true), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c16, some c70, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c160, c16, c70] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨28, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c5, some c186, some c344, some c134, some c158, some c68, some c935, some c191, some c11, some c139, some c42, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c132, c5, c186, c344, c134, c158, c68, c935, c191, c11, c139, c42] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c935 := derived935 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c934, some c132, some c936, some c343, some c133, some c158, some c306, some c352, some c220, some c252, some c254, some c212, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c934, c132, c936, c343, c133, c158, c306, c352, c220, c252, c254, c212] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c934 := derived934 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c936 := derived936 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c352 := h 351 (by decide)
  have h8 : Entails.eval a c220 := h 219 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨36, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c937, some c120, some c931, some c376, some c900, some c343, some c547, some c191, some c158, some c1, some c69, some c928, some c37, some c39, some c252, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c883, c937, c120, c931, c376, c900, c343, c547, c191, c158, c1, c69, c928, c37, c39, c252] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c937 := derived937 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c900 := derived900 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c928 := derived928 a h
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨6, by decide⟩, false), (⟨55, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c938, some c186, some c936, some c344, some c305, some c134, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c938, c186, c936, c344, c305, c134] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c938 := derived938 a h
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c936 := derived936 a h
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c939, some c132, some c883, some c937, some c120, some c931, some c5, some c186, some c589, some c305, some c134, some c146, some c314, some c933, some c142, some c71, some c117, some c225, some c210, some c253, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c939, c132, c883, c937, c120, c931, c5, c186, c589, c305, c134, c146, c314, c933, c142, c71, c117, c225, c210, c253] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c937 := derived937 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c314 := h 313 (by decide)
  have h13 : Entails.eval a c933 := derived933 a h
  have h14 : Entails.eval a c142 := h 141 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c225 := h 224 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c931, some c883, some c937, some c120, some c939, some c132, some c940, some c376, some c900, some c304, some c547, some c191, some c133, some c1, some c758, some c928, some c39, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c931, c883, c937, c120, c939, c132, c940, c376, c900, c304, c547, c191, c133, c1, c758, c928, c39] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c937 := derived937 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c940 := derived940 a h
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c900 := derived900 a h
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c547 := derived547 a h
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c1 := h 0 (by decide)
  have h14 : Entails.eval a c758 := derived758 a h
  have h15 : Entails.eval a c928 := derived928 a h
  have h16 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c366, some c359, some c168, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c366, c359, c168] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c366 := h 365 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, false), (⟨56, by decide⟩, true), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c165, some c168, some c362, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c165, c168, c362] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c165 := h 164 (by decide)
  have h1 : Entails.eval a c168 := h 167 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨44, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c88, some c123, some c54, some c148, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c233, c88, c123, c54, c148] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨22, by decide⟩, true), (⟨44, by decide⟩, true), (⟨45, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, true), (⟨56, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c117, some c249, some c943, some c944, some c368, some c290, some c356, some c229, some c216, some c243, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c24, c117, c249, c943, c944, c368, c290, c356, c229, c216, c243] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c943 := derived943 a h
  have h4 : Entails.eval a c944 := derived944 a h
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c931, some c883, some c305, some c146, some c304, some c52, some c314, some c142, some c942, some c288, some c567, some c945, some c210, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c589, c931, c883, c305, c146, c304, c52, c314, c142, c942, c288, c567, c945, c210] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c314 := h 313 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c942 := derived942 a h
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c567 := derived567 a h
  have h12 : Entails.eval a c945 := derived945 a h
  have h13 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c931, some c883, some c941, some c18, some c6, some c589, some c946, some c132, some c344, some c158, some c343, some c68, some c354, some c935, some c942, some c154, some c191, some c327, some c11, some c567, some c105, some c222, some c40, some c123, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c931, c883, c941, c18, c6, c589, c946, c132, c344, c158, c343, c68, c354, c935, c942, c154, c191, c327, c11, c567, c105, c222, c40, c123] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c941 := derived941 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c946 := derived946 a h
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c935 := derived935 a h
  have h14 : Entails.eval a c942 := derived942 a h
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c567 := derived567 a h
  have h20 : Entails.eval a c105 := h 104 (by decide)
  have h21 : Entails.eval a c222 := h 221 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  have h23 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c343, some c158, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c344, c343, c158] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c947, some c589, some c187, some c948, some c132, some c305, some c304, some c146, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c947, c589, c187, c948, c132, c305, c304, c146] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c947 := derived947 a h
  have h1 : Entails.eval a c589 := derived589 a h
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c948 := derived948 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c931, some c947, some c949, some c186, some c6, some c376, some c897, some c547, some c132, some c17, some c304, some c53, some c146, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c931, c947, c949, c186, c6, c376, c897, c547, c132, c17, c304, c53, c146] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c947 := derived947 a h
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c897 := derived897 a h
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c186, some c182, some c383, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c186, c182, c383] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c186 := h 185 (by decide)
  have h1 : Entails.eval a c182 := h 181 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c183, some c383, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c187, c183, c383] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false), (⟨38, by decide⟩, false), (⟨9, by decide⟩, false), (⟨16, by decide⟩, false), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c313, some c468, some c215, some c349, some c353, some c116, some c217, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c208, c313, c468, c215, c349, c353, c116, c217] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c468 := derived468 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c950, some c192, some c951, some c589, some c952, some c376, some c383, some c948, some c769, some c178, some c903, some c904, some c305, some c200, some c252, some c118, some c953, some c306, some c135, some c345, some c220, some c353, some c468, some c227, some c310, some c313, some c116, some c205, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c883, c950, c192, c951, c589, c952, c376, c383, c948, c769, c178, c903, c904, c305, c200, c252, c118, c953, c306, c135, c345, c220, c353, c468, c227, c310, c313, c116, c205] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c951 := derived951 a h
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c952 := derived952 a h
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c948 := derived948 a h
  have h9 : Entails.eval a c769 := derived769 a h
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c903 := derived903 a h
  have h12 : Entails.eval a c904 := derived904 a h
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c953 := derived953 a h
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c353 := h 352 (by decide)
  have h23 : Entails.eval a c468 := derived468 a h
  have h24 : Entails.eval a c227 := h 226 (by decide)
  have h25 : Entails.eval a c310 := h 309 (by decide)
  have h26 : Entails.eval a c313 := h 312 (by decide)
  have h27 : Entails.eval a c116 := h 115 (by decide)
  have h28 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨7, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c769, some c178, some c20, some c547, some c80, some c168, some c164, some c356, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c769, c178, c20, c547, c80, c168, c164, c356] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c769 := derived769 a h
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c547 := derived547 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨25, by decide⟩, true), (⟨49, by decide⟩, false), (⟨28, by decide⟩, true), (⟨54, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c333, some c267, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c344, c333, c267] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c154, some c66, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c158, c154, c66] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨28, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨52, by decide⟩, false), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c112, some c955, some c957, some c956, some c294, some c146, some c142, some c50, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c3, c112, c955, c957, c956, c294, c146, c142, c50] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c955 := derived955 a h
  have h3 : Entails.eval a c957 := derived957 a h
  have h4 : Entails.eval a c956 := derived956 a h
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c950, some c192, some c951, some c589, some c952, some c954, some c5, some c946, some c931, some c942, some c344, some c956, some c200, some c294, some c295, some c253, some c146, some c142, some c216, some c50, some c286, some c583, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c883, c950, c192, c951, c589, c952, c954, c5, c946, c931, c942, c344, c956, c200, c294, c295, c253, c146, c142, c216, c50, c286, c583] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c951 := derived951 a h
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c952 := derived952 a h
  have h6 : Entails.eval a c954 := derived954 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c946 := derived946 a h
  have h9 : Entails.eval a c931 := derived931 a h
  have h10 : Entails.eval a c942 := derived942 a h
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c956 := derived956 a h
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c295 := h 294 (by decide)
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c142 := h 141 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c50 := h 49 (by decide)
  have h21 : Entails.eval a c286 := h 285 (by decide)
  have h22 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c950, some c192, some c951, some c589, some c952, some c954, some c5, some c946, some c931, some c942, some c158, some c154, some c957, some c354, some c325, some c355, some c583, some c200, some c228, some c253, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c883, c950, c192, c951, c589, c952, c954, c5, c946, c931, c942, c158, c154, c957, c354, c325, c355, c583, c200, c228, c253] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c951 := derived951 a h
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c952 := derived952 a h
  have h6 : Entails.eval a c954 := derived954 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c946 := derived946 a h
  have h9 : Entails.eval a c931 := derived931 a h
  have h10 : Entails.eval a c942 := derived942 a h
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c957 := derived957 a h
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c583 := derived583 a h
  have h18 : Entails.eval a c200 := h 199 (by decide)
  have h19 : Entails.eval a c228 := h 227 (by decide)
  have h20 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c942, some c14, some c23, some c547, some c469, some c375, some c80, some c35, some c168, some c466, some c74, some c105, some c109, some c88, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c942, c14, c23, c547, c469, c375, c80, c35, c168, c466, c74, c105, c109, c88] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c942 := derived942 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c547 := derived547 a h
  have h4 : Entails.eval a c469 := derived469 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c466 := derived466 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c469, some c375, some c88, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c469, c375, c88] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c469 := derived469 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c931, some c883, some c950, some c192, some c951, some c589, some c952, some c954, some c5, some c942, some c946, some c958, some c960, some c344, some c959, some c200, some c253, some c249, some c961, some c471, some c112, some c962, some c234, some c543, some c80, some c235, some c547, some c20, some c40, some c128, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c931, c883, c950, c192, c951, c589, c952, c954, c5, c942, c946, c958, c960, c344, c959, c200, c253, c249, c961, c471, c112, c962, c234, c543, c80, c235, c547, c20, c40, c128] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c950 := derived950 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c951 := derived951 a h
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c952 := derived952 a h
  have h7 : Entails.eval a c954 := derived954 a h
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c942 := derived942 a h
  have h10 : Entails.eval a c946 := derived946 a h
  have h11 : Entails.eval a c958 := derived958 a h
  have h12 : Entails.eval a c960 := derived960 a h
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c959 := derived959 a h
  have h15 : Entails.eval a c200 := h 199 (by decide)
  have h16 : Entails.eval a c253 := h 252 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  have h18 : Entails.eval a c961 := derived961 a h
  have h19 : Entails.eval a c471 := derived471 a h
  have h20 : Entails.eval a c112 := h 111 (by decide)
  have h21 : Entails.eval a c962 := derived962 a h
  have h22 : Entails.eval a c234 := h 233 (by decide)
  have h23 : Entails.eval a c543 := derived543 a h
  have h24 : Entails.eval a c80 := h 79 (by decide)
  have h25 : Entails.eval a c235 := h 234 (by decide)
  have h26 : Entails.eval a c547 := derived547 a h
  have h27 : Entails.eval a c20 := h 19 (by decide)
  have h28 : Entails.eval a c40 := h 39 (by decide)
  have h29 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨45, by decide⟩, false), (⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨12, by decide⟩, false), (⟨44, by decide⟩, false), (⟨7, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨10, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c166, some c74, some c843, some c192, some c769, some c706, some c368, some c27, some c92, some c128, some c251, some c534, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c166, c74, c843, c192, c769, c706, c368, c27, c92, c128, c251, c534] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c706 := derived706 a h
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c534 := derived534 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c146, some c142, some c50, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c146, c142, c50] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c146 := h 145 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c294, some c129, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 57) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c333, c294, c129] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c963, some c931, some c883, some c111, some c112, some c76, some c4, some c166, some c192, some c74, some c951, some c957, some c589, some c843, some c952, some c20, some c191, some c965, some c966, some c769, some c383, some c942, some c964, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 57) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c963, c931, c883, c111, c112, c76, c4, c166, c192, c74, c951, c957, c589, c843, c952, c20, c191, c965, c966, c769, c383, c942, c964] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c192 := h 191 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c951 := derived951 a h
  have h11 : Entails.eval a c957 := derived957 a h
  have h12 : Entails.eval a c589 := derived589 a h
  have h13 : Entails.eval a c843 := derived843 a h
  have h14 : Entails.eval a c952 := derived952 a h
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c191 := h 190 (by decide)
  have h17 : Entails.eval a c965 := derived965 a h
  have h18 : Entails.eval a c966 := derived966 a h
  have h19 : Entails.eval a c769 := derived769 a h
  have h20 : Entails.eval a c383 := h 382 (by decide)
  have h21 : Entails.eval a c942 := derived942 a h
  have h22 : Entails.eval a c964 := derived964 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c968 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c967, some c963, some c931, some c883, some c14, some c3, some c952, some c843, some c383, some c918, some c74, some c942, some c191, some c168, some c884, some c80, some c364, some c106, some c166, some c371, some c82, some c4, some c583, some c368, some c69, some c27, some c132, some c156, some c288, some c70, some c133, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 57) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c589, c967, c963, c931, c883, c14, c3, c952, c843, c383, c918, c74, c942, c191, c168, c884, c80, c364, c106, c166, c371, c82, c4, c583, c368, c69, c27, c132, c156, c288, c70, c133] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c967 := derived967 a h
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c883 := derived883 a h
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c952 := derived952 a h
  have h8 : Entails.eval a c843 := derived843 a h
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c918 := derived918 a h
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c942 := derived942 a h
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c168 := h 167 (by decide)
  have h15 : Entails.eval a c884 := derived884 a h
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c106 := h 105 (by decide)
  have h19 : Entails.eval a c166 := h 165 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c82 := h 81 (by decide)
  have h22 : Entails.eval a c4 := h 3 (by decide)
  have h23 : Entails.eval a c583 := derived583 a h
  have h24 : Entails.eval a c368 := h 367 (by decide)
  have h25 : Entails.eval a c69 := h 68 (by decide)
  have h26 : Entails.eval a c27 := h 26 (by decide)
  have h27 : Entails.eval a c132 := h 131 (by decide)
  have h28 : Entails.eval a c156 := h 155 (by decide)
  have h29 : Entails.eval a c288 := h 287 (by decide)
  have h30 : Entails.eval a c70 := h 69 (by decide)
  have h31 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨38, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c132, some c53, some c52, some c146, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 57) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c69, c132, c53, c52, c146] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c68, some c156, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 57) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c70, c68, c156] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c971 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c970, some c133, some c52, some c54, some c144, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 57) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c970, c133, c52, c54, c144] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c970 := derived970 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c972 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c884, some c969, some c971, some c20, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 57) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c4, c884, c969, c971, c20] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c884 := derived884 a h
  have h2 : Entails.eval a c969 := derived969 a h
  have h3 : Entails.eval a c971 := derived971 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c931, some c589, some c963, some c968, some c192, some c185, some c972, some c191, some c179, some c376, some c942, some c967, some c333, some c966, some c129, some c146, some c277, some c41, some c82, some c21, some c375, some c243, some c27, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 57) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c883, c931, c589, c963, c968, c192, c185, c972, c191, c179, c376, c942, c967, c333, c966, c129, c146, c277, c41, c82, c21, c375, c243, c27] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c942 := derived942 a h
  have h12 : Entails.eval a c967 := derived967 a h
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c966 := derived966 a h
  have h15 : Entails.eval a c129 := h 128 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c41 := h 40 (by decide)
  have h19 : Entails.eval a c82 := h 81 (by decide)
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c375 := h 374 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c931, some c589, some c963, some c968, some c192, some c185, some c972, some c191, some c179, some c376, some c942, some c967, some c973, some c134, some c158, some c294, some c129, some c57, some c316, some c82, some c21, some c375, some c243, some c27, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 57) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c883, c931, c589, c963, c968, c192, c185, c972, c191, c179, c376, c942, c967, c973, c134, c158, c294, c129, c57, c316, c82, c21, c375, c243, c27] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c963 := derived963 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c942 := derived942 a h
  have h12 : Entails.eval a c967 := derived967 a h
  have h13 : Entails.eval a c973 := derived973 a h
  have h14 : Entails.eval a c134 := h 133 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c82 := h 81 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c375 := h 374 (by decide)
  have h23 : Entails.eval a c243 := h 242 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c974, some c105, some c883, some c931, some c589, some c963, some c968, some c192, some c185, some c972, some c191, some c179, some c376, some c942, some c134, some c158, some c294, some c70, some c129, some c316, some c21, some c242, some c243, some c228, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 57) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c974, c105, c883, c931, c589, c963, c968, c192, c185, c972, c191, c179, c376, c942, c134, c158, c294, c70, c129, c316, c21, c242, c243, c228] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c974 := derived974 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c931 := derived931 a h
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c968 := derived968 a h
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c972 := derived972 a h
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c179 := h 178 (by decide)
  have h12 : Entails.eval a c376 := h 375 (by decide)
  have h13 : Entails.eval a c942 := derived942 a h
  have h14 : Entails.eval a c134 := h 133 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c242 := h 241 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c963, some c931, some c883, some c589, some c968, some c192, some c185, some c972, some c191, some c179, some c376, some c942, some c974, some c105, some c975, some c333, some c966, some c129, some c146, some c295, some c277, some c21, some c242, some c243, some c216, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 57) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c963, c931, c883, c589, c968, c192, c185, c972, c191, c179, c376, c942, c974, c105, c975, c333, c966, c129, c146, c295, c277, c21, c242, c243, c216] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c589 := derived589 a h
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c972 := derived972 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c942 := derived942 a h
  have h12 : Entails.eval a c974 := derived974 a h
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c975 := derived975 a h
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c966 := derived966 a h
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c146 := h 145 (by decide)
  have h19 : Entails.eval a c295 := h 294 (by decide)
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c242 := h 241 (by decide)
  have h23 : Entails.eval a c243 := h 242 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c963, some c931, some c883, some c967, some c976, some c186, some c6, some c951, some c376, some c383, some c192, some c443, some c179, some c768, some c75, some c94, some c972, some c163, some c109, some c165, some c105, some c85, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 57) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c963, c931, c883, c967, c976, c186, c6, c951, c376, c383, c192, c443, c179, c768, c75, c94, c972, c163, c109, c165, c105, c85] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c883 := derived883 a h
  have h3 : Entails.eval a c967 := derived967 a h
  have h4 : Entails.eval a c976 := derived976 a h
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c951 := derived951 a h
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c443 := derived443 a h
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c768 := derived768 a h
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c972 := derived972 a h
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c105 := h 104 (by decide)
  have h21 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c931, some c963, some c977, some c5, some c18, some c376, some c383, some c704, some c443, some c547, some c419, some c164, some c191, some c80, some c903, some c904, some c705, some c905, some c192, some c4, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 57) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c883, c931, c963, c977, c5, c18, c376, c383, c704, c443, c547, c419, c164, c191, c80, c903, c904, c705, c905, c192, c4] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c977 := derived977 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c704 := derived704 a h
  have h9 : Entails.eval a c443 := derived443 a h
  have h10 : Entails.eval a c547 := derived547 a h
  have h11 : Entails.eval a c419 := derived419 a h
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c903 := derived903 a h
  have h16 : Entails.eval a c904 := derived904 a h
  have h17 : Entails.eval a c705 := derived705 a h
  have h18 : Entails.eval a c905 := derived905 a h
  have h19 : Entails.eval a c192 := h 191 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c883, some c978, some c193, some c194, some c900, some c185, some c743, some c135, some c616, some c308, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 57) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c5, c883, c978, c193, c194, c900, c185, c743, c135, c616, c308] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c883 := derived883 a h
  have h2 : Entails.eval a c978 := derived978 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c900 := derived900 a h
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c743 := derived743 a h
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c616 := derived616 a h
  have h10 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨11, by decide⟩, false), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c383, some c376, some c883, some c978, some c194, some c19, some c589, some c78, some c361, some c547, some c110, some c165, some c85, some c22, some c119, some c248, some c240, some c604, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 57) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c5, c383, c376, c883, c978, c194, c19, c589, c78, c361, c547, c110, c165, c85, c22, c119, c248, c240, c604] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c883 := derived883 a h
  have h4 : Entails.eval a c978 := derived978 a h
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c589 := derived589 a h
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c547 := derived547 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c604 := derived604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c145, some c304, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 57) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c147, c145, c304] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨11, by decide⟩, false), (⟨47, by decide⟩, true), (⟨46, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c883, some c978, some c194, some c193, some c5, some c383, some c980, some c894, some c981, some c19, some c78, some c361, some c110, some c165, some c84, some c22, some c119, some c117, some c240, some c254, some c55, some c214, some c210, some c286, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 57) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c883, c978, c194, c193, c5, c383, c980, c894, c981, c19, c78, c361, c110, c165, c84, c22, c119, c117, c240, c254, c55, c214, c210, c286] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c883 := derived883 a h
  have h1 : Entails.eval a c978 := derived978 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c980 := derived980 a h
  have h7 : Entails.eval a c894 := derived894 a h
  have h8 : Entails.eval a c981 := derived981 a h
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c240 := h 239 (by decide)
  have h19 : Entails.eval a c254 := h 253 (by decide)
  have h20 : Entails.eval a c55 := h 54 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c210 := h 209 (by decide)
  have h23 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c979, some c163, some c978, some c162, some c5, some c383, some c376, some c883, some c194, some c19, some c980, some c894, some c982, some c380, some c547, some c26, some c92, some c114, some c253, some c119, some c107, some c31, some c29, some c94, some c108, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 57) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c979, c163, c978, c162, c5, c383, c376, c883, c194, c19, c980, c894, c982, c380, c547, c26, c92, c114, c253, c119, c107, c31, c29, c94, c108] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c979 := derived979 a h
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c978 := derived978 a h
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c883 := derived883 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c980 := derived980 a h
  have h11 : Entails.eval a c894 := derived894 a h
  have h12 : Entails.eval a c982 := derived982 a h
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c547 := derived547 a h
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c119 := h 118 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c31 := h 30 (by decide)
  have h22 : Entails.eval a c29 := h 28 (by decide)
  have h23 : Entails.eval a c94 := h 93 (by decide)
  have h24 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived983

end CochromaticTwenty.Certificates.B16_2_2
