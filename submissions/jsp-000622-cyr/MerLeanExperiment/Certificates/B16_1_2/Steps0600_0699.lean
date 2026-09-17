import MerLeanExperiment.Certificates.B16_1_2.Steps0500_0599

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c994 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c993, some c983, some c1, some c29, some c655, some c387, some c256, some c200, some c44, some c533, some c126, some c121, some c42, some c985, some c303, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c993, c983, c1, c29, c655, c387, c256, c200, c44, c533, c126, c121, c42, c985, c303] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c993 := derived993 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c533 := derived533 a h
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c985 := derived985 a h
  have h14 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨49, by decide⟩, true), (⟨32, by decide⟩, false), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c655, some c985, some c319, some c200, some c90, some c828, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c983, c655, c985, c319, c200, c90, c828] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c985 := derived985 a h
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c828 := derived828 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨31, by decide⟩, false), (⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c533, some c25, some c204, some c23, some c154, some c124, some c328, some c27, some c33, some c125, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c533, c25, c204, c23, c154, c124, c328, c27, c33, c125] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c533 := derived533 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c997 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c993, some c15, some c983, some c1, some c29, some c994, some c85, some c995, some c121, some c533, some c200, some c319, some c160, some c996, some c176, some c797, some c44, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 57) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c655, c993, c15, c983, c1, c29, c994, c85, c995, c121, c533, c200, c319, c160, c996, c176, c797, c44] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c993 := derived993 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c994 := derived994 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c995 := derived995 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c533 := derived533 a h
  have h11 : Entails.eval a c200 := h 199 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c996 := derived996 a h
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c797 := derived797 a h
  have h17 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c993, some c15, some c983, some c1, some c29, some c843, some c985, some c995, some c319, some c256, some c200, some c90, some c179, some c174, some c303, some c370, some c987, some c385, some c673, some c114, some c841, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 57) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c655, c993, c15, c983, c1, c29, c843, c985, c995, c319, c256, c200, c90, c179, c174, c303, c370, c987, c385, c673, c114, c841] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c993 := derived993 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c843 := derived843 a h
  have h7 : Entails.eval a c985 := derived985 a h
  have h8 : Entails.eval a c995 := derived995 a h
  have h9 : Entails.eval a c319 := h 318 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c200 := h 199 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c303 := h 302 (by decide)
  have h16 : Entails.eval a c370 := h 369 (by decide)
  have h17 : Entails.eval a c987 := derived987 a h
  have h18 : Entails.eval a c385 := h 384 (by decide)
  have h19 : Entails.eval a c673 := derived673 a h
  have h20 : Entails.eval a c114 := h 113 (by decide)
  have h21 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c998, some c997, some c122, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c998, c997, c122] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c997 := derived997 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c993, some c15, some c983, some c1, some c29, some c843, some c998, some c999, some c105, some c57, some c86, some c984, some c387, some c256, some c326, some c296, some c200, some c206, some c205, some c126, some c214, some c83, some c169, some c81, some c59, some c324, some c294, some c58, some c222, some c249, some c124, some c272, some c275, some c48, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c655, c993, c15, c983, c1, c29, c843, c998, c999, c105, c57, c86, c984, c387, c256, c326, c296, c200, c206, c205, c126, c214, c83, c169, c81, c59, c324, c294, c58, c222, c249, c124, c272, c275, c48] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c993 := derived993 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c843 := derived843 a h
  have h7 : Entails.eval a c998 := derived998 a h
  have h8 : Entails.eval a c999 := derived999 a h
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c984 := derived984 a h
  have h13 : Entails.eval a c387 := h 386 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c326 := h 325 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c206 := h 205 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c126 := h 125 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c83 := h 82 (by decide)
  have h23 : Entails.eval a c169 := h 168 (by decide)
  have h24 : Entails.eval a c81 := h 80 (by decide)
  have h25 : Entails.eval a c59 := h 58 (by decide)
  have h26 : Entails.eval a c324 := h 323 (by decide)
  have h27 : Entails.eval a c294 := h 293 (by decide)
  have h28 : Entails.eval a c58 := h 57 (by decide)
  have h29 : Entails.eval a c222 := h 221 (by decide)
  have h30 : Entails.eval a c249 := h 248 (by decide)
  have h31 : Entails.eval a c124 := h 123 (by decide)
  have h32 : Entails.eval a c272 := h 271 (by decide)
  have h33 : Entails.eval a c275 := h 274 (by decide)
  have h34 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1000, some c993, some c983, some c1, some c29, some c843, some c655, some c105, some c57, some c86, some c387, some c256, some c200, some c36, some c216, some c206, some c205, some c126, some c179, some c157, some c90, some c325, some c83, some c214, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c1000, c993, c983, c1, c29, c843, c655, c105, c57, c86, c387, c256, c200, c36, c216, c206, c205, c126, c179, c157, c90, c325, c83, c214] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c1000 := derived1000 a h
  have h1 : Entails.eval a c993 := derived993 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c655 := derived655 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c256 := h 255 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c216 := h 215 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c205 := h 204 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c90 := h 89 (by decide)
  have h21 : Entails.eval a c325 := h 324 (by decide)
  have h22 : Entails.eval a c83 := h 82 (by decide)
  have h23 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c29, some c1, some c1001, some c122, some c985, some c1000, some c993, some c655, some c200, some c90, some c206, some c205, some c828, some c148, some c157, some c76, some c345, some c325, some c277, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c983, c29, c1, c1001, c122, c985, c1000, c993, c655, c200, c90, c206, c205, c828, c148, c157, c76, c345, c325, c277] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c1001 := derived1001 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c985 := derived985 a h
  have h6 : Entails.eval a c1000 := derived1000 a h
  have h7 : Entails.eval a c993 := derived993 a h
  have h8 : Entails.eval a c655 := derived655 a h
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c828 := derived828 a h
  have h14 : Entails.eval a c148 := h 147 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c345 := h 344 (by decide)
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨49, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c29, some c126, some c828, some c42, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c1, c29, c126, c828, c42] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨14, by decide⟩, true), (⟨54, by decide⟩, false), (⟨8, by decide⟩, false), (⟨15, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c15, some c84, some c356, some c172, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c655, c15, c84, c356, c172] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨17, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c216, some c148, some c797, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c983, c216, c148, c797] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c797 := derived797 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c29, some c1000, some c1005, some c1001, some c993, some c122, some c1002, some c387, some c1004, some c1003, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c983, c29, c1000, c1005, c1001, c993, c122, c1002, c387, c1004, c1003] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c1000 := derived1000 a h
  have h3 : Entails.eval a c1005 := derived1005 a h
  have h4 : Entails.eval a c1001 := derived1001 a h
  have h5 : Entails.eval a c993 := derived993 a h
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c1002 := derived1002 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c1004 := derived1004 a h
  have h10 : Entails.eval a c1003 := derived1003 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1007 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c29, some c1000, some c1006, some c8, some c36, some c797, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1007 : lratChecker f1007 p1007 = .success := by decide +kernel
theorem unsat1007 : Unsatisfiable (PosFin 57) f1007 := by
  apply lratCheckerSound f1007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1007
  · intro a ha; simp [p1007] at ha; subst a; trivial
  · exact checked1007
theorem derived1007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1007 := by
  apply localUnsat_implies_entails f1007 [c983, c29, c1000, c1006, c8, c36, c797] c1007 unsat1007 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c1000 := derived1000 a h
  have h3 : Entails.eval a c1006 := derived1006 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c797 := derived797 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1008 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨22, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨2, by decide⟩, false), (⟨41, by decide⟩, false), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c290, some c42, some c121, some c107, some c65, some c317, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1008 : lratChecker f1008 p1008 = .success := by decide +kernel
theorem unsat1008 : Unsatisfiable (PosFin 57) f1008 := by
  apply lratCheckerSound f1008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1008
  · intro a ha; simp [p1008] at ha; subst a; trivial
  · exact checked1008
theorem derived1008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1008 := by
  apply localUnsat_implies_entails f1008 [c290, c42, c121, c107, c65, c317] c1008 unsat1008 (by rfl) a
  have h0 : Entails.eval a c290 := h 289 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1009 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨2, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c36, some c762, some c8, some c843, some c655, some c387, some c267, some c9, some c203, some c176, some c1008, some c34, some c160, some c121, some c321, some c291, some c101, some c226, some c370, some c916, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1009 : lratChecker f1009 p1009 = .success := by decide +kernel
theorem unsat1009 : Unsatisfiable (PosFin 57) f1009 := by
  apply lratCheckerSound f1009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1009
  · intro a ha; simp [p1009] at ha; subst a; trivial
  · exact checked1009
theorem derived1009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1009 := by
  apply localUnsat_implies_entails f1009 [c983, c36, c762, c8, c843, c655, c387, c267, c9, c203, c176, c1008, c34, c160, c121, c321, c291, c101, c226, c370, c916] c1009 unsat1009 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c843 := derived843 a h
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c1008 := derived1008 a h
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c160 := h 159 (by decide)
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c321 := h 320 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c226 := h 225 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c916 := derived916 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1010 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c983, some c843, some c655, some c8, some c36, some c206, some c762, some c132, some c797, some c45, some c1009, some c200, some c14, some c203, some c140, some c121, some c19, some c65, some c204, some c912, some c514, some c370, some c221, some c291, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1010 : lratChecker f1010 p1010 = .success := by decide +kernel
theorem unsat1010 : Unsatisfiable (PosFin 57) f1010 := by
  apply lratCheckerSound f1010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1010
  · intro a ha; simp [p1010] at ha; subst a; trivial
  · exact checked1010
theorem derived1010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1010 := by
  apply localUnsat_implies_entails f1010 [c1007, c983, c843, c655, c8, c36, c206, c762, c132, c797, c45, c1009, c200, c14, c203, c140, c121, c19, c65, c204, c912, c514, c370, c221, c291] c1010 unsat1010 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c762 := derived762 a h
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c797 := derived797 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c1009 := derived1009 a h
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c65 := h 64 (by decide)
  have h19 : Entails.eval a c204 := h 203 (by decide)
  have h20 : Entails.eval a c912 := derived912 a h
  have h21 : Entails.eval a c514 := derived514 a h
  have h22 : Entails.eval a c370 := h 369 (by decide)
  have h23 : Entails.eval a c221 := h 220 (by decide)
  have h24 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1011 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c6, some c203, some c201, some c121, some c158, some c25, some c815, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1011 : lratChecker f1011 p1011 = .success := by decide +kernel
theorem unsat1011 : Unsatisfiable (PosFin 57) f1011 := by
  apply lratCheckerSound f1011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1011
  · intro a ha; simp [p1011] at ha; subst a; trivial
  · exact checked1011
theorem derived1011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1011 := by
  apply localUnsat_implies_entails f1011 [c160, c6, c203, c201, c121, c158, c25, c815] c1011 unsat1011 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c815 := derived815 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1012 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c983, some c1007, some c1010, some c308, some c105, some c9, some c323, some c322, some c655, some c657, some c1011, some c533, some c828, some c121, some c90, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1012 : lratChecker f1012 p1012 = .success := by decide +kernel
theorem unsat1012 : Unsatisfiable (PosFin 57) f1012 := by
  apply lratCheckerSound f1012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1012
  · intro a ha; simp [p1012] at ha; subst a; trivial
  · exact checked1012
theorem derived1012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1012 := by
  apply localUnsat_implies_entails f1012 [c843, c983, c1007, c1010, c308, c105, c9, c323, c322, c655, c657, c1011, c533, c828, c121, c90] c1012 unsat1012 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c1007 := derived1007 a h
  have h3 : Entails.eval a c1010 := derived1010 a h
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c322 := h 321 (by decide)
  have h9 : Entails.eval a c655 := derived655 a h
  have h10 : Entails.eval a c657 := derived657 a h
  have h11 : Entails.eval a c1011 := derived1011 a h
  have h12 : Entails.eval a c533 := derived533 a h
  have h13 : Entails.eval a c828 := derived828 a h
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1013 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c983, some c843, some c655, some c1010, some c308, some c322, some c323, some c9, some c85, some c105, some c292, some c44, some c1012, some c267, some c34, some c214, some c121, some c356, some c533, some c107, some c101, some c160, some c354, some c203, some c175, some c169, some c370, some c178, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1013 : lratChecker f1013 p1013 = .success := by decide +kernel
theorem unsat1013 : Unsatisfiable (PosFin 57) f1013 := by
  apply lratCheckerSound f1013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1013
  · intro a ha; simp [p1013] at ha; subst a; trivial
  · exact checked1013
theorem derived1013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1013 := by
  apply localUnsat_implies_entails f1013 [c1007, c983, c843, c655, c1010, c308, c322, c323, c9, c85, c105, c292, c44, c1012, c267, c34, c214, c121, c356, c533, c107, c101, c160, c354, c203, c175, c169, c370, c178] c1013 unsat1013 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c1010 := derived1010 a h
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c1012 := derived1012 a h
  have h14 : Entails.eval a c267 := h 266 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c533 := derived533 a h
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c101 := h 100 (by decide)
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c354 := h 353 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c175 := h 174 (by decide)
  have h26 : Entails.eval a c169 := h 168 (by decide)
  have h27 : Entails.eval a c370 := h 369 (by decide)
  have h28 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1014 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1014 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c843, some c387, some c425, some c983, some c85, some c9, some c1007, some c655, some c6, some c322, some c290, some c42, some c267, some c216, some c1004, some c772, some c201, some c91, some c370, some c26, some c124, some c22, some c98, some c177, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1014 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1014 : lratChecker f1014 p1014 = .success := by decide +kernel
theorem unsat1014 : Unsatisfiable (PosFin 57) f1014 := by
  apply lratCheckerSound f1014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1014
  · intro a ha; simp [p1014] at ha; subst a; trivial
  · exact checked1014
theorem derived1014 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1014 := by
  apply localUnsat_implies_entails f1014 [c1013, c843, c387, c425, c983, c85, c9, c1007, c655, c6, c322, c290, c42, c267, c216, c1004, c772, c201, c91, c370, c26, c124, c22, c98, c177] c1014 unsat1014 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c1007 := derived1007 a h
  have h8 : Entails.eval a c655 := derived655 a h
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c322 := h 321 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c267 := h 266 (by decide)
  have h14 : Entails.eval a c216 := h 215 (by decide)
  have h15 : Entails.eval a c1004 := derived1004 a h
  have h16 : Entails.eval a c772 := derived772 a h
  have h17 : Entails.eval a c201 := h 200 (by decide)
  have h18 : Entails.eval a c91 := h 90 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c22 := h 21 (by decide)
  have h23 : Entails.eval a c98 := h 97 (by decide)
  have h24 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1015 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1015 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c148, some c157, some c76, some c325, some c210, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1015 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1015 : lratChecker f1015 p1015 = .success := by decide +kernel
theorem unsat1015 : Unsatisfiable (PosFin 57) f1015 := by
  apply lratCheckerSound f1015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1015
  · intro a ha; simp [p1015] at ha; subst a; trivial
  · exact checked1015
theorem derived1015 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1015 := by
  apply localUnsat_implies_entails f1015 [c322, c148, c157, c76, c325, c210] c1015 unsat1015 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1016 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1016 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c843, some c387, some c425, some c983, some c1014, some c828, some c42, some c267, some c9, some c126, some c131, some c205, some c206, some c105, some c85, some c1007, some c655, some c148, some c157, some c76, some c772, some c229, some c210, some c370, some c332, some c294, some c249, some c373, some c265, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1016 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1016 : lratChecker f1016 p1016 = .success := by decide +kernel
theorem unsat1016 : Unsatisfiable (PosFin 57) f1016 := by
  apply lratCheckerSound f1016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1016
  · intro a ha; simp [p1016] at ha; subst a; trivial
  · exact checked1016
theorem derived1016 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1016 := by
  apply localUnsat_implies_entails f1016 [c1013, c843, c387, c425, c983, c1014, c828, c42, c267, c9, c126, c131, c205, c206, c105, c85, c1007, c655, c148, c157, c76, c772, c229, c210, c370, c332, c294, c249, c373, c265] c1016 unsat1016 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c1014 := derived1014 a h
  have h6 : Entails.eval a c828 := derived828 a h
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c1007 := derived1007 a h
  have h17 : Entails.eval a c655 := derived655 a h
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c157 := h 156 (by decide)
  have h20 : Entails.eval a c76 := h 75 (by decide)
  have h21 : Entails.eval a c772 := derived772 a h
  have h22 : Entails.eval a c229 := h 228 (by decide)
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c370 := h 369 (by decide)
  have h25 : Entails.eval a c332 := h 331 (by decide)
  have h26 : Entails.eval a c294 := h 293 (by decide)
  have h27 : Entails.eval a c249 := h 248 (by decide)
  have h28 : Entails.eval a c373 := h 372 (by decide)
  have h29 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1017 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false), (⟨8, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1017 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c387, some c425, some c68, some c356, some c84, some c288, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1017 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1017 : lratChecker f1017 p1017 = .success := by decide +kernel
theorem unsat1017 : Unsatisfiable (PosFin 57) f1017 := by
  apply lratCheckerSound f1017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1017
  · intro a ha; simp [p1017] at ha; subst a; trivial
  · exact checked1017
theorem derived1017 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1017 := by
  apply localUnsat_implies_entails f1017 [c843, c387, c425, c68, c356, c84, c288] c1017 unsat1017 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c425 := derived425 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1018 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, true), (⟨7, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1018 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c282, some c79, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1018 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1018 : lratChecker f1018 p1018 = .success := by decide +kernel
theorem unsat1018 : Unsatisfiable (PosFin 57) f1018 := by
  apply lratCheckerSound f1018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1018
  · intro a ha; simp [p1018] at ha; subst a; trivial
  · exact checked1018
theorem derived1018 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1018 := by
  apply localUnsat_implies_entails f1018 [c62, c282, c79] c1018 unsat1018 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1019 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨39, by decide⟩, false), (⟨38, by decide⟩, true), (⟨7, by decide⟩, false), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1019 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c286, some c82, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1019 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1019 : lratChecker f1019 p1019 = .success := by decide +kernel
theorem unsat1019 : Unsatisfiable (PosFin 57) f1019 := by
  apply lratCheckerSound f1019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1019
  · intro a ha; simp [p1019] at ha; subst a; trivial
  · exact checked1019
theorem derived1019 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1019 := by
  apply localUnsat_implies_entails f1019 [c66, c286, c82] c1019 unsat1019 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1020 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨40, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1020 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c288, some c1018, some c1019, some c289, some c327, some c102, some c156, some c82, some c201, some c171, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1020 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1020 : lratChecker f1020 p1020 = .success := by decide +kernel
theorem unsat1020 : Unsatisfiable (PosFin 57) f1020 := by
  apply lratCheckerSound f1020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1020
  · intro a ha; simp [p1020] at ha; subst a; trivial
  · exact checked1020
theorem derived1020 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1020 := by
  apply localUnsat_implies_entails f1020 [c68, c288, c1018, c1019, c289, c327, c102, c156, c82, c201, c171] c1020 unsat1020 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c1018 := derived1018 a h
  have h3 : Entails.eval a c1019 := derived1019 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1021 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1021 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c1007, some c983, some c843, some c655, some c387, some c9, some c85, some c105, some c425, some c1014, some c206, some c205, some c828, some c42, some c131, some c1015, some c1016, some c323, some c1017, some c169, some c1020, some c354, some c12, some c196, some c120, some c175, some c98, some c370, some c373, some c381, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1021 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1021 : lratChecker f1021 p1021 = .success := by decide +kernel
theorem unsat1021 : Unsatisfiable (PosFin 57) f1021 := by
  apply lratCheckerSound f1021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1021
  · intro a ha; simp [p1021] at ha; subst a; trivial
  · exact checked1021
theorem derived1021 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1021 := by
  apply localUnsat_implies_entails f1021 [c1013, c1007, c983, c843, c655, c387, c9, c85, c105, c425, c1014, c206, c205, c828, c42, c131, c1015, c1016, c323, c1017, c169, c1020, c354, c12, c196, c120, c175, c98, c370, c373, c381] c1021 unsat1021 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c1007 := derived1007 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c387 := h 386 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c425 := derived425 a h
  have h10 : Entails.eval a c1014 := derived1014 a h
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c828 := derived828 a h
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c1015 := derived1015 a h
  have h17 : Entails.eval a c1016 := derived1016 a h
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c1017 := derived1017 a h
  have h20 : Entails.eval a c169 := h 168 (by decide)
  have h21 : Entails.eval a c1020 := derived1020 a h
  have h22 : Entails.eval a c354 := h 353 (by decide)
  have h23 : Entails.eval a c12 := h 11 (by decide)
  have h24 : Entails.eval a c196 := h 195 (by decide)
  have h25 : Entails.eval a c120 := h 119 (by decide)
  have h26 : Entails.eval a c175 := h 174 (by decide)
  have h27 : Entails.eval a c98 := h 97 (by decide)
  have h28 : Entails.eval a c370 := h 369 (by decide)
  have h29 : Entails.eval a c373 := h 372 (by decide)
  have h30 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1022 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1022 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c1015, some c229, some c210, some c985, some c324, some c19, some c62, some c120, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1022 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1022 : lratChecker f1022 p1022 = .success := by decide +kernel
theorem unsat1022 : Unsatisfiable (PosFin 57) f1022 := by
  apply lratCheckerSound f1022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1022
  · intro a ha; simp [p1022] at ha; subst a; trivial
  · exact checked1022
theorem derived1022 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1022 := by
  apply localUnsat_implies_entails f1022 [c122, c1015, c229, c210, c985, c324, c19, c62, c120] c1022 unsat1022 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c1015 := derived1015 a h
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c985 := derived985 a h
  have h5 : Entails.eval a c324 := h 323 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1023 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1023 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1021, some c1013, some c1007, some c983, some c655, some c122, some c116, some c14, some c90, some c206, some c205, some c828, some c308, some c148, some c157, some c345, some c76, some c84, some c1022, some c131, some c34, some c290, some c325, some c301, some c37, some c762, some c281, some c95, some c321, some c120, some c159, some c227, some c50, some c125, some c134, some c18, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1023 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked1023 : lratChecker f1023 p1023 = .success := by decide +kernel
theorem unsat1023 : Unsatisfiable (PosFin 57) f1023 := by
  apply lratCheckerSound f1023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1023
  · intro a ha; simp [p1023] at ha; subst a; trivial
  · exact checked1023
theorem derived1023 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1023 := by
  apply localUnsat_implies_entails f1023 [c1021, c1013, c1007, c983, c655, c122, c116, c14, c90, c206, c205, c828, c308, c148, c157, c345, c76, c84, c1022, c131, c34, c290, c325, c301, c37, c762, c281, c95, c321, c120, c159, c227, c50, c125, c134, c18] c1023 unsat1023 (by rfl) a
  have h0 : Entails.eval a c1021 := derived1021 a h
  have h1 : Entails.eval a c1013 := derived1013 a h
  have h2 : Entails.eval a c1007 := derived1007 a h
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c828 := derived828 a h
  have h12 : Entails.eval a c308 := h 307 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c76 := h 75 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  have h18 : Entails.eval a c1022 := derived1022 a h
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c290 := h 289 (by decide)
  have h22 : Entails.eval a c325 := h 324 (by decide)
  have h23 : Entails.eval a c301 := h 300 (by decide)
  have h24 : Entails.eval a c37 := h 36 (by decide)
  have h25 : Entails.eval a c762 := derived762 a h
  have h26 : Entails.eval a c281 := h 280 (by decide)
  have h27 : Entails.eval a c95 := h 94 (by decide)
  have h28 : Entails.eval a c321 := h 320 (by decide)
  have h29 : Entails.eval a c120 := h 119 (by decide)
  have h30 : Entails.eval a c159 := h 158 (by decide)
  have h31 : Entails.eval a c227 := h 226 (by decide)
  have h32 : Entails.eval a c50 := h 49 (by decide)
  have h33 : Entails.eval a c125 := h 124 (by decide)
  have h34 : Entails.eval a c134 := h 133 (by decide)
  have h35 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1024 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨54, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1024 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c90, some c179, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1024 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1024 : lratChecker f1024 p1024 = .success := by decide +kernel
theorem unsat1024 : Unsatisfiable (PosFin 57) f1024 := by
  apply lratCheckerSound f1024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1024
  · intro a ha; simp [p1024] at ha; subst a; trivial
  · exact checked1024
theorem derived1024 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1024 := by
  apply localUnsat_implies_entails f1024 [c14, c90, c179] c1024 unsat1024 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1025 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨42, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1025 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c177, some c129, some c39, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1025 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1025 : lratChecker f1025 p1025 = .success := by decide +kernel
theorem unsat1025 : Unsatisfiable (PosFin 57) f1025 := by
  apply lratCheckerSound f1025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1025
  · intro a ha; simp [p1025] at ha; subst a; trivial
  · exact checked1025
theorem derived1025 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1025 := by
  apply localUnsat_implies_entails f1025 [c18, c177, c129, c39] c1025 unsat1025 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1026 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨26, by decide⟩, true), (⟨18, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1026 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1023, some c86, some c983, some c105, some c655, some c109, some c1007, some c19, some c1025, some c124, some c492, some c60, some c305, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1026 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1026 : lratChecker f1026 p1026 = .success := by decide +kernel
theorem unsat1026 : Unsatisfiable (PosFin 57) f1026 := by
  apply lratCheckerSound f1026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1026
  · intro a ha; simp [p1026] at ha; subst a; trivial
  · exact checked1026
theorem derived1026 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1026 := by
  apply localUnsat_implies_entails f1026 [c843, c1023, c86, c983, c105, c655, c109, c1007, c19, c1025, c124, c492, c60, c305] c1026 unsat1026 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1023 := derived1023 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c655 := derived655 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1007 := derived1007 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c1025 := derived1025 a h
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c492 := derived492 a h
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1027 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨9, by decide⟩, false), (⟨18, by decide⟩, false), (⟨40, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1027 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c1021, some c843, some c1023, some c86, some c1024, some c83, some c655, some c109, some c84, some c1007, some c983, some c105, some c308, some c716, some c131, some c377, some c240, some c772, some c37, some c762, some c269, some c127, some c250, some c227, some c147, some c302, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1027 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1027 : lratChecker f1027 p1027 = .success := by decide +kernel
theorem unsat1027 : Unsatisfiable (PosFin 57) f1027 := by
  apply lratCheckerSound f1027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1027
  · intro a ha; simp [p1027] at ha; subst a; trivial
  · exact checked1027
theorem derived1027 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1027 := by
  apply localUnsat_implies_entails f1027 [c1013, c1021, c843, c1023, c86, c1024, c83, c655, c109, c84, c1007, c983, c105, c308, c716, c131, c377, c240, c772, c37, c762, c269, c127, c250, c227, c147, c302] c1027 unsat1027 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c1021 := derived1021 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c1023 := derived1023 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c1024 := derived1024 a h
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c1007 := derived1007 a h
  have h11 : Entails.eval a c983 := derived983 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c716 := derived716 a h
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c377 := h 376 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c772 := derived772 a h
  have h19 : Entails.eval a c37 := h 36 (by decide)
  have h20 : Entails.eval a c762 := derived762 a h
  have h21 : Entails.eval a c269 := h 268 (by decide)
  have h22 : Entails.eval a c127 := h 126 (by decide)
  have h23 : Entails.eval a c250 := h 249 (by decide)
  have h24 : Entails.eval a c227 := h 226 (by decide)
  have h25 : Entails.eval a c147 := h 146 (by decide)
  have h26 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1028 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨18, by decide⟩, false), (⟨40, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1028 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c843, some c983, some c1023, some c105, some c308, some c1021, some c655, some c1027, some c656, some c200, some c305, some c498, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1028 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1028 : lratChecker f1028 p1028 = .success := by decide +kernel
theorem unsat1028 : Unsatisfiable (PosFin 57) f1028 := by
  apply lratCheckerSound f1028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1028
  · intro a ha; simp [p1028] at ha; subst a; trivial
  · exact checked1028
theorem derived1028 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1028 := by
  apply localUnsat_implies_entails f1028 [c1007, c843, c983, c1023, c105, c308, c1021, c655, c1027, c656, c200, c305, c498] c1028 unsat1028 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1023 := derived1023 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c1021 := derived1021 a h
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c1027 := derived1027 a h
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  have h12 : Entails.eval a c498 := derived498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1029 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨40, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1029 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1013, some c1021, some c843, some c1023, some c86, some c1024, some c83, some c1028, some c821, some c1026, some c325, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1029 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1029 : lratChecker f1029 p1029 = .success := by decide +kernel
theorem unsat1029 : Unsatisfiable (PosFin 57) f1029 := by
  apply lratCheckerSound f1029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1029
  · intro a ha; simp [p1029] at ha; subst a; trivial
  · exact checked1029
theorem derived1029 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1029 := by
  apply localUnsat_implies_entails f1029 [c1013, c1021, c843, c1023, c86, c1024, c83, c1028, c821, c1026, c325] c1029 unsat1029 (by rfl) a
  have h0 : Entails.eval a c1013 := derived1013 a h
  have h1 : Entails.eval a c1021 := derived1021 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c1023 := derived1023 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c1024 := derived1024 a h
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c1028 := derived1028 a h
  have h8 : Entails.eval a c821 := derived821 a h
  have h9 : Entails.eval a c1026 := derived1026 a h
  have h10 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1030 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1030 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c843, some c983, some c1023, some c105, some c308, some c148, some c1013, some c1021, some c86, some c1024, some c83, some c655, some c109, some c84, some c345, some c157, some c1029, some c732, some c30, some c325, some c324, some c146, some c214, some c288, some c282, some c126, some c321, some c163, some c286, some c364, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1030 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1030 : lratChecker f1030 p1030 = .success := by decide +kernel
theorem unsat1030 : Unsatisfiable (PosFin 57) f1030 := by
  apply lratCheckerSound f1030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1030
  · intro a ha; simp [p1030] at ha; subst a; trivial
  · exact checked1030
theorem derived1030 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1030 := by
  apply localUnsat_implies_entails f1030 [c1007, c843, c983, c1023, c105, c308, c148, c1013, c1021, c86, c1024, c83, c655, c109, c84, c345, c157, c1029, c732, c30, c325, c324, c146, c214, c288, c282, c126, c321, c163, c286, c364] c1030 unsat1030 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1023 := derived1023 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c1013 := derived1013 a h
  have h8 : Entails.eval a c1021 := derived1021 a h
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c1024 := derived1024 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c655 := derived655 a h
  have h13 : Entails.eval a c109 := h 108 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c1029 := derived1029 a h
  have h18 : Entails.eval a c732 := derived732 a h
  have h19 : Entails.eval a c30 := h 29 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c146 := h 145 (by decide)
  have h23 : Entails.eval a c214 := h 213 (by decide)
  have h24 : Entails.eval a c288 := h 287 (by decide)
  have h25 : Entails.eval a c282 := h 281 (by decide)
  have h26 : Entails.eval a c126 := h 125 (by decide)
  have h27 : Entails.eval a c321 := h 320 (by decide)
  have h28 : Entails.eval a c163 := h 162 (by decide)
  have h29 : Entails.eval a c286 := h 285 (by decide)
  have h30 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1031 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1031 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c48, some c253, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p1031 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1031 : lratChecker f1031 p1031 = .success := by decide +kernel
theorem unsat1031 : Unsatisfiable (PosFin 57) f1031 := by
  apply lratCheckerSound f1031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1031
  · intro a ha; simp [p1031] at ha; subst a; trivial
  · exact checked1031
theorem derived1031 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1031 := by
  apply localUnsat_implies_entails f1031 [c108, c48, c253] c1031 unsat1031 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1032 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1032 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1007, some c843, some c983, some c1023, some c105, some c308, some c1030, some c204, some c155, some c148, some c1013, some c1021, some c86, some c1024, some c83, some c205, some c146, some c655, some c109, some c45, some c30, some c295, some c293, some c377, some c1031, some c673, some c124, some c772, some c18, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1032 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1032 : lratChecker f1032 p1032 = .success := by decide +kernel
theorem unsat1032 : Unsatisfiable (PosFin 57) f1032 := by
  apply lratCheckerSound f1032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1032
  · intro a ha; simp [p1032] at ha; subst a; trivial
  · exact checked1032
theorem derived1032 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1032 := by
  apply localUnsat_implies_entails f1032 [c1007, c843, c983, c1023, c105, c308, c1030, c204, c155, c148, c1013, c1021, c86, c1024, c83, c205, c146, c655, c109, c45, c30, c295, c293, c377, c1031, c673, c124, c772, c18] c1032 unsat1032 (by rfl) a
  have h0 : Entails.eval a c1007 := derived1007 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c1023 := derived1023 a h
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c308 := h 307 (by decide)
  have h6 : Entails.eval a c1030 := derived1030 a h
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c1013 := derived1013 a h
  have h11 : Entails.eval a c1021 := derived1021 a h
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c1024 := derived1024 a h
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c205 := h 204 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c655 := derived655 a h
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c30 := h 29 (by decide)
  have h21 : Entails.eval a c295 := h 294 (by decide)
  have h22 : Entails.eval a c293 := h 292 (by decide)
  have h23 : Entails.eval a c377 := h 376 (by decide)
  have h24 : Entails.eval a c1031 := derived1031 a h
  have h25 : Entails.eval a c673 := derived673 a h
  have h26 : Entails.eval a c124 := h 123 (by decide)
  have h27 : Entails.eval a c772 := derived772 a h
  have h28 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1033 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1033 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1021, some c843, some c1023, some c86, some c1024, some c1007, some c983, some c105, some c308, some c655, some c109, some c1013, some c148, some c345, some c84, some c83, some c1030, some c205, some c204, some c178, some c200, some c166, some c1032, some c130, some c1028, some c40, some c1025, some c77, some c492, some c231, some c236, some c305, some c256, some c506, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1033 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked1033 : lratChecker f1033 p1033 = .success := by decide +kernel
theorem unsat1033 : Unsatisfiable (PosFin 57) f1033 := by
  apply lratCheckerSound f1033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1033
  · intro a ha; simp [p1033] at ha; subst a; trivial
  · exact checked1033
theorem derived1033 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1033 := by
  apply localUnsat_implies_entails f1033 [c1021, c843, c1023, c86, c1024, c1007, c983, c105, c308, c655, c109, c1013, c148, c345, c84, c83, c1030, c205, c204, c178, c200, c166, c1032, c130, c1028, c40, c1025, c77, c492, c231, c236, c305, c256, c506] c1033 unsat1033 (by rfl) a
  have h0 : Entails.eval a c1021 := derived1021 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c1023 := derived1023 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c1024 := derived1024 a h
  have h5 : Entails.eval a c1007 := derived1007 a h
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c655 := derived655 a h
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c1013 := derived1013 a h
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c1030 := derived1030 a h
  have h17 : Entails.eval a c205 := h 204 (by decide)
  have h18 : Entails.eval a c204 := h 203 (by decide)
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  have h21 : Entails.eval a c166 := h 165 (by decide)
  have h22 : Entails.eval a c1032 := derived1032 a h
  have h23 : Entails.eval a c130 := h 129 (by decide)
  have h24 : Entails.eval a c1028 := derived1028 a h
  have h25 : Entails.eval a c40 := h 39 (by decide)
  have h26 : Entails.eval a c1025 := derived1025 a h
  have h27 : Entails.eval a c77 := h 76 (by decide)
  have h28 : Entails.eval a c492 := derived492 a h
  have h29 : Entails.eval a c231 := h 230 (by decide)
  have h30 : Entails.eval a c236 := h 235 (by decide)
  have h31 : Entails.eval a c305 := h 304 (by decide)
  have h32 : Entails.eval a c256 := h 255 (by decide)
  have h33 : Entails.eval a c506 := derived506 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1034 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1034 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1033, some c655, some c1021, some c206, some c200, some c203, some c843, some c1023, some c86, some c1024, some c1007, some c983, some c105, some c308, some c109, some c1013, some c132, some c1025, some c216, some c124, some c84, some c83, some c108, some c146, some c305, some c60, some c227, some c5, some c325, some c138, some c225, some c240, some c273, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1034 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1034 : lratChecker f1034 p1034 = .success := by decide +kernel
theorem unsat1034 : Unsatisfiable (PosFin 57) f1034 := by
  apply lratCheckerSound f1034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1034
  · intro a ha; simp [p1034] at ha; subst a; trivial
  · exact checked1034
theorem derived1034 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1034 := by
  apply localUnsat_implies_entails f1034 [c1033, c655, c1021, c206, c200, c203, c843, c1023, c86, c1024, c1007, c983, c105, c308, c109, c1013, c132, c1025, c216, c124, c84, c83, c108, c146, c305, c60, c227, c5, c325, c138, c225, c240, c273] c1034 unsat1034 (by rfl) a
  have h0 : Entails.eval a c1033 := derived1033 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c1021 := derived1021 a h
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c843 := derived843 a h
  have h7 : Entails.eval a c1023 := derived1023 a h
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c1024 := derived1024 a h
  have h10 : Entails.eval a c1007 := derived1007 a h
  have h11 : Entails.eval a c983 := derived983 a h
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  have h15 : Entails.eval a c1013 := derived1013 a h
  have h16 : Entails.eval a c132 := h 131 (by decide)
  have h17 : Entails.eval a c1025 := derived1025 a h
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c84 := h 83 (by decide)
  have h21 : Entails.eval a c83 := h 82 (by decide)
  have h22 : Entails.eval a c108 := h 107 (by decide)
  have h23 : Entails.eval a c146 := h 145 (by decide)
  have h24 : Entails.eval a c305 := h 304 (by decide)
  have h25 : Entails.eval a c60 := h 59 (by decide)
  have h26 : Entails.eval a c227 := h 226 (by decide)
  have h27 : Entails.eval a c5 := h 4 (by decide)
  have h28 : Entails.eval a c325 := h 324 (by decide)
  have h29 : Entails.eval a c138 := h 137 (by decide)
  have h30 : Entails.eval a c225 := h 224 (by decide)
  have h31 : Entails.eval a c240 := h 239 (by decide)
  have h32 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1035 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1035 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c843, some c655, some c1007, some c1013, some c1021, some c1023, some c109, some c105, some c86, some c308, some c1024, some c1033, some c206, some c200, some c203, some c1034, some c45, some c1005, some c1031, some c345, some c83, some c124, some c18, some c204, some c208, some c19, some c163, some c170, some c80, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1035 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1035 : lratChecker f1035 p1035 = .success := by decide +kernel
theorem unsat1035 : Unsatisfiable (PosFin 57) f1035 := by
  apply lratCheckerSound f1035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1035
  · intro a ha; simp [p1035] at ha; subst a; trivial
  · exact checked1035
theorem derived1035 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1035 := by
  apply localUnsat_implies_entails f1035 [c983, c843, c655, c1007, c1013, c1021, c1023, c109, c105, c86, c308, c1024, c1033, c206, c200, c203, c1034, c45, c1005, c1031, c345, c83, c124, c18, c204, c208, c19, c163, c170, c80] c1035 unsat1035 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c1007 := derived1007 a h
  have h4 : Entails.eval a c1013 := derived1013 a h
  have h5 : Entails.eval a c1021 := derived1021 a h
  have h6 : Entails.eval a c1023 := derived1023 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c1024 := derived1024 a h
  have h12 : Entails.eval a c1033 := derived1033 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c1034 := derived1034 a h
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c1005 := derived1005 a h
  have h19 : Entails.eval a c1031 := derived1031 a h
  have h20 : Entails.eval a c345 := h 344 (by decide)
  have h21 : Entails.eval a c83 := h 82 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  have h24 : Entails.eval a c204 := h 203 (by decide)
  have h25 : Entails.eval a c208 := h 207 (by decide)
  have h26 : Entails.eval a c19 := h 18 (by decide)
  have h27 : Entails.eval a c163 := h 162 (by decide)
  have h28 : Entails.eval a c170 := h 169 (by decide)
  have h29 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1036 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨34, by decide⟩, false), (⟨16, by decide⟩, false), (⟨26, by decide⟩, false), (⟨32, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1036 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c655, some c193, some c76, some c363, some c854, some c36, some c733, some c370, some c377, some c295, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1036 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1036 : lratChecker f1036 p1036 = .success := by decide +kernel
theorem unsat1036 : Unsatisfiable (PosFin 57) f1036 := by
  apply lratCheckerSound f1036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1036
  · intro a ha; simp [p1036] at ha; subst a; trivial
  · exact checked1036
theorem derived1036 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1036 := by
  apply localUnsat_implies_entails f1036 [c843, c1035, c10, c655, c193, c76, c363, c854, c36, c733, c370, c377, c295] c1036 unsat1036 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c854 := derived854 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c733 := derived733 a h
  have h10 : Entails.eval a c370 := h 369 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1037 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1037 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c655, some c843, some c1035, some c193, some c983, some c1, some c18, some c308, some c208, some c192, some c305, some c152, some c159, some c5, some c145, some c82, some c342, some c161, some c1036, some c216, some c762, some c140, some c215, some c291, some c370, some c377, some c335, some c295, some c733, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1037 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1037 : lratChecker f1037 p1037 = .success := by decide +kernel
theorem unsat1037 : Unsatisfiable (PosFin 57) f1037 := by
  apply lratCheckerSound f1037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1037
  · intro a ha; simp [p1037] at ha; subst a; trivial
  · exact checked1037
theorem derived1037 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1037 := by
  apply localUnsat_implies_entails f1037 [c387, c655, c843, c1035, c193, c983, c1, c18, c308, c208, c192, c305, c152, c159, c5, c145, c82, c342, c161, c1036, c216, c762, c140, c215, c291, c370, c377, c335, c295, c733] c1037 unsat1037 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c1035 := derived1035 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c145 := h 144 (by decide)
  have h16 : Entails.eval a c82 := h 81 (by decide)
  have h17 : Entails.eval a c342 := h 341 (by decide)
  have h18 : Entails.eval a c161 := h 160 (by decide)
  have h19 : Entails.eval a c1036 := derived1036 a h
  have h20 : Entails.eval a c216 := h 215 (by decide)
  have h21 : Entails.eval a c762 := derived762 a h
  have h22 : Entails.eval a c140 := h 139 (by decide)
  have h23 : Entails.eval a c215 := h 214 (by decide)
  have h24 : Entails.eval a c291 := h 290 (by decide)
  have h25 : Entails.eval a c370 := h 369 (by decide)
  have h26 : Entails.eval a c377 := h 376 (by decide)
  have h27 : Entails.eval a c335 := h 334 (by decide)
  have h28 : Entails.eval a c295 := h 294 (by decide)
  have h29 : Entails.eval a c733 := derived733 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1038 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1038 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c29, some c843, some c1035, some c10, some c326, some c324, some c985, some c59, some c121, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1038 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1038 : lratChecker f1038 p1038 = .success := by decide +kernel
theorem unsat1038 : Unsatisfiable (PosFin 57) f1038 := by
  apply lratCheckerSound f1038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1038
  · intro a ha; simp [p1038] at ha; subst a; trivial
  · exact checked1038
theorem derived1038 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1038 := by
  apply localUnsat_implies_entails f1038 [c983, c29, c843, c1035, c10, c326, c324, c985, c59, c121] c1038 unsat1038 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c1035 := derived1035 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c326 := h 325 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c985 := derived985 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1039 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1039 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c843, some c1035, some c193, some c201, some c983, some c308, some c29, some c58, some c127, some c1038, some c152, some c221, some c328, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1039 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1039 : lratChecker f1039 p1039 = .success := by decide +kernel
theorem unsat1039 : Unsatisfiable (PosFin 57) f1039 := by
  apply lratCheckerSound f1039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1039
  · intro a ha; simp [p1039] at ha; subst a; trivial
  · exact checked1039
theorem derived1039 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1039 := by
  apply localUnsat_implies_entails f1039 [c655, c843, c1035, c193, c201, c983, c308, c29, c58, c127, c1038, c152, c221, c328] c1039 unsat1039 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c1038 := derived1038 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1040 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1040 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c843, some c1035, some c10, some c655, some c193, some c983, some c201, some c203, some c192, some c1039, some c498, some c8, some c148, some c305, some c76, some c29, some c741, some c127, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1040 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1040 : lratChecker f1040 p1040 = .success := by decide +kernel
theorem unsat1040 : Unsatisfiable (PosFin 57) f1040 := by
  apply lratCheckerSound f1040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1040
  · intro a ha; simp [p1040] at ha; subst a; trivial
  · exact checked1040
theorem derived1040 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1040 := by
  apply localUnsat_implies_entails f1040 [c387, c843, c1035, c10, c655, c193, c983, c201, c203, c192, c1039, c498, c8, c148, c305, c76, c29, c741, c127] c1040 unsat1040 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c498 := derived498 a h
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c741 := derived741 a h
  have h18 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1041 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1041 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c655, some c843, some c1035, some c193, some c983, some c1040, some c18, some c1037, some c208, some c116, some c865, some c878, some c192, some c392, some c87, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1041 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1041 : lratChecker f1041 p1041 = .success := by decide +kernel
theorem unsat1041 : Unsatisfiable (PosFin 57) f1041 := by
  apply lratCheckerSound f1041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1041
  · intro a ha; simp [p1041] at ha; subst a; trivial
  · exact checked1041
theorem derived1041 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1041 := by
  apply localUnsat_implies_entails f1041 [c387, c655, c843, c1035, c193, c983, c1040, c18, c1037, c208, c116, c865, c878, c192, c392, c87] c1041 unsat1041 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c1035 := derived1035 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c1040 := derived1040 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c1037 := derived1037 a h
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c865 := derived865 a h
  have h12 : Entails.eval a c878 := derived878 a h
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c392 := h 391 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1042 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1042 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c655, some c193, some c983, some c91, some c116, some c122, some c8, some c36, some c762, some c140, some c291, some c35, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1042 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1042 : lratChecker f1042 p1042 = .success := by decide +kernel
theorem unsat1042 : Unsatisfiable (PosFin 57) f1042 := by
  apply lratCheckerSound f1042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1042
  · intro a ha; simp [p1042] at ha; subst a; trivial
  · exact checked1042
theorem derived1042 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1042 := by
  apply localUnsat_implies_entails f1042 [c843, c1035, c10, c655, c193, c983, c91, c116, c122, c8, c36, c762, c140, c291, c35] c1042 unsat1042 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c762 := derived762 a h
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1043 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1043 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c120, some c387, some c983, some c1, some c19, some c308, some c1042, some c124, some c763, some c122, some c14, some c90, some c831, some c114, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1043 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1043 : lratChecker f1043 p1043 = .success := by decide +kernel
theorem unsat1043 : Unsatisfiable (PosFin 57) f1043 := by
  apply lratCheckerSound f1043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1043
  · intro a ha; simp [p1043] at ha; subst a; trivial
  · exact checked1043
theorem derived1043 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1043 := by
  apply localUnsat_implies_entails f1043 [c843, c1035, c10, c120, c387, c983, c1, c19, c308, c1042, c124, c763, c122, c14, c90, c831, c114] c1043 unsat1043 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c1042 := derived1042 a h
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c763 := derived763 a h
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c831 := derived831 a h
  have h16 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1044 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1044 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c192, some c387, some c10, some c983, some c27, some c5, some c122, some c14, some c840, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1044 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1044 : lratChecker f1044 p1044 = .success := by decide +kernel
theorem unsat1044 : Unsatisfiable (PosFin 57) f1044 := by
  apply lratCheckerSound f1044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1044
  · intro a ha; simp [p1044] at ha; subst a; trivial
  · exact checked1044
theorem derived1044 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1044 := by
  apply localUnsat_implies_entails f1044 [c843, c1035, c192, c387, c10, c983, c27, c5, c122, c14, c840] c1044 unsat1044 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c840 := derived840 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1045 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨18, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1045 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c655, some c193, some c983, some c387, some c1041, some c1043, some c201, some c203, some c1044, some c124, some c91, some c116, some c175, some c122, some c37, some c762, some c8, some c127, some c44, some c35, some c304, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1045 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1045 : lratChecker f1045 p1045 = .success := by decide +kernel
theorem unsat1045 : Unsatisfiable (PosFin 57) f1045 := by
  apply lratCheckerSound f1045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1045
  · intro a ha; simp [p1045] at ha; subst a; trivial
  · exact checked1045
theorem derived1045 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1045 := by
  apply localUnsat_implies_entails f1045 [c843, c1035, c10, c655, c193, c983, c387, c1041, c1043, c201, c203, c1044, c124, c91, c116, c175, c122, c37, c762, c8, c127, c44, c35, c304] c1045 unsat1045 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c1041 := derived1041 a h
  have h8 : Entails.eval a c1043 := derived1043 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c1044 := derived1044 a h
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c116 := h 115 (by decide)
  have h15 : Entails.eval a c175 := h 174 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c762 := derived762 a h
  have h19 : Entails.eval a c8 := h 7 (by decide)
  have h20 : Entails.eval a c127 := h 126 (by decide)
  have h21 : Entails.eval a c44 := h 43 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1046 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1046 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c843, some c983, some c9, some c1035, some c193, some c85, some c175, some c370, some c10, some c790, some c377, some c14, some c382, some c383, some c121, some c122, some c101, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1046 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1046 : lratChecker f1046 p1046 = .success := by decide +kernel
theorem unsat1046 : Unsatisfiable (PosFin 57) f1046 := by
  apply lratCheckerSound f1046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1046
  · intro a ha; simp [p1046] at ha; subst a; trivial
  · exact checked1046
theorem derived1046 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1046 := by
  apply localUnsat_implies_entails f1046 [c655, c843, c983, c9, c1035, c193, c85, c175, c370, c10, c790, c377, c14, c382, c383, c121, c122, c101] c1046 unsat1046 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c370 := h 369 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c790 := derived790 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c383 := h 382 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1047 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1047 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c983, some c9, some c843, some c1035, some c193, some c85, some c175, some c91, some c895, some c192, some c913, some c10, some c121, some c122, some c107, some c27, some c392, some c124, some c106, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1047 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1047 : lratChecker f1047 p1047 = .success := by decide +kernel
theorem unsat1047 : Unsatisfiable (PosFin 57) f1047 := by
  apply lratCheckerSound f1047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1047
  · intro a ha; simp [p1047] at ha; subst a; trivial
  · exact checked1047
theorem derived1047 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1047 := by
  apply localUnsat_implies_entails f1047 [c655, c983, c9, c843, c1035, c193, c85, c175, c91, c895, c192, c913, c10, c121, c122, c107, c27, c392, c124, c106] c1047 unsat1047 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c983 := derived983 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c895 := derived895 a h
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c913 := derived913 a h
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c107 := h 106 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c392 := h 391 (by decide)
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1048 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1048 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1047, some c1046, some c1035, some c913, some c983, some c85, some c9, some c8, some c319, some c985, some c34, some c29, some c267, some c292, some c44, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1048 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1048 : lratChecker f1048 p1048 = .success := by decide +kernel
theorem unsat1048 : Unsatisfiable (PosFin 57) f1048 := by
  apply lratCheckerSound f1048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1048
  · intro a ha; simp [p1048] at ha; subst a; trivial
  · exact checked1048
theorem derived1048 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1048 := by
  apply localUnsat_implies_entails f1048 [c1047, c1046, c1035, c913, c983, c85, c9, c8, c319, c985, c34, c29, c267, c292, c44] c1048 unsat1048 (by rfl) a
  have h0 : Entails.eval a c1047 := derived1047 a h
  have h1 : Entails.eval a c1046 := derived1046 a h
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c913 := derived913 a h
  have h4 : Entails.eval a c983 := derived983 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c985 := derived985 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1049 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨30, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1049 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c1047, some c6, some c828, some c1046, some c34, some c267, some c1048, some c843, some c1035, some c895, some c192, some c9, some c655, some c193, some c85, some c175, some c422, some c392, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1049 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1049 : lratChecker f1049 p1049 = .success := by decide +kernel
theorem unsat1049 : Unsatisfiable (PosFin 57) f1049 := by
  apply lratCheckerSound f1049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1049
  · intro a ha; simp [p1049] at ha; subst a; trivial
  · exact checked1049
theorem derived1049 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1049 := by
  apply localUnsat_implies_entails f1049 [c983, c1047, c6, c828, c1046, c34, c267, c1048, c843, c1035, c895, c192, c9, c655, c193, c85, c175, c422, c392] c1049 unsat1049 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c1047 := derived1047 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c1046 := derived1046 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c1048 := derived1048 a h
  have h8 : Entails.eval a c843 := derived843 a h
  have h9 : Entails.eval a c1035 := derived1035 a h
  have h10 : Entails.eval a c895 := derived895 a h
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c655 := derived655 a h
  have h14 : Entails.eval a c193 := h 192 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c422 := derived422 a h
  have h18 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1050 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1050 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1047, some c655, some c843, some c983, some c9, some c1035, some c193, some c85, some c175, some c370, some c10, some c6, some c828, some c1049, some c107, some c373, some c120, some c381, some c98, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1050 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1050 : lratChecker f1050 p1050 = .success := by decide +kernel
theorem unsat1050 : Unsatisfiable (PosFin 57) f1050 := by
  apply lratCheckerSound f1050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1050
  · intro a ha; simp [p1050] at ha; subst a; trivial
  · exact checked1050
theorem derived1050 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1050 := by
  apply localUnsat_implies_entails f1050 [c1047, c655, c843, c983, c9, c1035, c193, c85, c175, c370, c10, c6, c828, c1049, c107, c373, c120, c381, c98] c1050 unsat1050 (by rfl) a
  have h0 : Entails.eval a c1047 := derived1047 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c828 := derived828 a h
  have h13 : Entails.eval a c1049 := derived1049 a h
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c120 := h 119 (by decide)
  have h17 : Entails.eval a c381 := h 380 (by decide)
  have h18 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1051 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1051 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c655, some c193, some c983, some c1045, some c9, some c85, some c913, some c175, some c91, some c370, some c1046, some c1047, some c1048, some c1050, some c319, some c498, some c148, some c76, some c84, some c142, some c233, some c325, some c295, some c127, some c577, some c42, some c229, some c102, some c267, some c124, some c225, some c46, some c275, some c332, some c251, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1051 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked1051 : lratChecker f1051 p1051 = .success := by decide +kernel
theorem unsat1051 : Unsatisfiable (PosFin 57) f1051 := by
  apply lratCheckerSound f1051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1051
  · intro a ha; simp [p1051] at ha; subst a; trivial
  · exact checked1051
theorem derived1051 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1051 := by
  apply localUnsat_implies_entails f1051 [c843, c1035, c10, c655, c193, c983, c1045, c9, c85, c913, c175, c91, c370, c1046, c1047, c1048, c1050, c319, c498, c148, c76, c84, c142, c233, c325, c295, c127, c577, c42, c229, c102, c267, c124, c225, c46, c275, c332, c251] c1051 unsat1051 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c983 := derived983 a h
  have h6 : Entails.eval a c1045 := derived1045 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c913 := derived913 a h
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c1046 := derived1046 a h
  have h14 : Entails.eval a c1047 := derived1047 a h
  have h15 : Entails.eval a c1048 := derived1048 a h
  have h16 : Entails.eval a c1050 := derived1050 a h
  have h17 : Entails.eval a c319 := h 318 (by decide)
  have h18 : Entails.eval a c498 := derived498 a h
  have h19 : Entails.eval a c148 := h 147 (by decide)
  have h20 : Entails.eval a c76 := h 75 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c142 := h 141 (by decide)
  have h23 : Entails.eval a c233 := h 232 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  have h25 : Entails.eval a c295 := h 294 (by decide)
  have h26 : Entails.eval a c127 := h 126 (by decide)
  have h27 : Entails.eval a c577 := derived577 a h
  have h28 : Entails.eval a c42 := h 41 (by decide)
  have h29 : Entails.eval a c229 := h 228 (by decide)
  have h30 : Entails.eval a c102 := h 101 (by decide)
  have h31 : Entails.eval a c267 := h 266 (by decide)
  have h32 : Entails.eval a c124 := h 123 (by decide)
  have h33 : Entails.eval a c225 := h 224 (by decide)
  have h34 : Entails.eval a c46 := h 45 (by decide)
  have h35 : Entails.eval a c275 := h 274 (by decide)
  have h36 : Entails.eval a c332 := h 331 (by decide)
  have h37 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1052 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1052 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c843, some c1035, some c10, some c655, some c193, some c983, some c9, some c85, some c913, some c1046, some c1047, some c1048, some c1050, some c175, some c319, some c370, some c148, some c76, some c142, some c325, some c295, some c42, some c267, some c273, some c225, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1052 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1052 : lratChecker f1052 p1052 = .success := by decide +kernel
theorem unsat1052 : Unsatisfiable (PosFin 57) f1052 := by
  apply lratCheckerSound f1052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1052
  · intro a ha; simp [p1052] at ha; subst a; trivial
  · exact checked1052
theorem derived1052 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1052 := by
  apply localUnsat_implies_entails f1052 [c1051, c843, c1035, c10, c655, c193, c983, c9, c85, c913, c1046, c1047, c1048, c1050, c175, c319, c370, c148, c76, c142, c325, c295, c42, c267, c273, c225] c1052 unsat1052 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c843 := derived843 a h
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c913 := derived913 a h
  have h10 : Entails.eval a c1046 := derived1046 a h
  have h11 : Entails.eval a c1047 := derived1047 a h
  have h12 : Entails.eval a c1048 := derived1048 a h
  have h13 : Entails.eval a c1050 := derived1050 a h
  have h14 : Entails.eval a c175 := h 174 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c370 := h 369 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c76 := h 75 (by decide)
  have h19 : Entails.eval a c142 := h 141 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  have h21 : Entails.eval a c295 := h 294 (by decide)
  have h22 : Entails.eval a c42 := h 41 (by decide)
  have h23 : Entails.eval a c267 := h 266 (by decide)
  have h24 : Entails.eval a c273 := h 272 (by decide)
  have h25 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1053 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨56, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1053 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1037, some c1043, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1053 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1053 : lratChecker f1053 p1053 = .success := by decide +kernel
theorem unsat1053 : Unsatisfiable (PosFin 57) f1053 := by
  apply lratCheckerSound f1053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1053
  · intro a ha; simp [p1053] at ha; subst a; trivial
  · exact checked1053
theorem derived1053 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1053 := by
  apply localUnsat_implies_entails f1053 [c1037, c1043] c1053 unsat1053 (by rfl) a
  have h0 : Entails.eval a c1037 := derived1037 a h
  have h1 : Entails.eval a c1043 := derived1043 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1054 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1054 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1052, some c387, some c655, some c116, some c843, some c1035, some c193, some c1053, some c201, some c203, some c1044, some c124, some c110, some c192, some c983, some c305, some c58, some c314, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1054 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1054 : lratChecker f1054 p1054 = .success := by decide +kernel
theorem unsat1054 : Unsatisfiable (PosFin 57) f1054 := by
  apply lratCheckerSound f1054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1054
  · intro a ha; simp [p1054] at ha; subst a; trivial
  · exact checked1054
theorem derived1054 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1054 := by
  apply localUnsat_implies_entails f1054 [c1052, c387, c655, c116, c843, c1035, c193, c1053, c201, c203, c1044, c124, c110, c192, c983, c305, c58, c314] c1054 unsat1054 (by rfl) a
  have h0 : Entails.eval a c1052 := derived1052 a h
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c843 := derived843 a h
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c193 := h 192 (by decide)
  have h7 : Entails.eval a c1053 := derived1053 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c1044 := derived1044 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c983 := derived983 a h
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1055 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1055 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1052, some c387, some c655, some c843, some c1035, some c193, some c983, some c116, some c14, some c1053, some c201, some c203, some c790, some c37, some c1054, some c985, some c152, some c159, some c326, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1055 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1055 : lratChecker f1055 p1055 = .success := by decide +kernel
theorem unsat1055 : Unsatisfiable (PosFin 57) f1055 := by
  apply lratCheckerSound f1055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1055
  · intro a ha; simp [p1055] at ha; subst a; trivial
  · exact checked1055
theorem derived1055 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1055 := by
  apply localUnsat_implies_entails f1055 [c1052, c387, c655, c843, c1035, c193, c983, c116, c14, c1053, c201, c203, c790, c37, c1054, c985, c152, c159, c326] c1055 unsat1055 (by rfl) a
  have h0 : Entails.eval a c1052 := derived1052 a h
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c983 := derived983 a h
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c1053 := derived1053 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c790 := derived790 a h
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c1054 := derived1054 a h
  have h15 : Entails.eval a c985 := derived985 a h
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1056 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1056 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c843, some c1035, some c10, some c1055, some c122, some c121, some c1052, some c1051, some c655, some c193, some c983, some c201, some c203, some c27, some c8, some c308, some c29, some c256, some c127, some c53, some c44, some c272, some c51, some c124, some c91, some c35, some c304, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1056 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1056 : lratChecker f1056 p1056 = .success := by decide +kernel
theorem unsat1056 : Unsatisfiable (PosFin 57) f1056 := by
  apply lratCheckerSound f1056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1056
  · intro a ha; simp [p1056] at ha; subst a; trivial
  · exact checked1056
theorem derived1056 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1056 := by
  apply localUnsat_implies_entails f1056 [c843, c1035, c10, c1055, c122, c121, c1052, c1051, c655, c193, c983, c201, c203, c27, c8, c308, c29, c256, c127, c53, c44, c272, c51, c124, c91, c35, c304] c1056 unsat1056 (by rfl) a
  have h0 : Entails.eval a c843 := derived843 a h
  have h1 : Entails.eval a c1035 := derived1035 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c1055 := derived1055 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c1052 := derived1052 a h
  have h7 : Entails.eval a c1051 := derived1051 a h
  have h8 : Entails.eval a c655 := derived655 a h
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c983 := derived983 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c127 := h 126 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c272 := h 271 (by decide)
  have h22 : Entails.eval a c51 := h 50 (by decide)
  have h23 : Entails.eval a c124 := h 123 (by decide)
  have h24 : Entails.eval a c91 := h 90 (by decide)
  have h25 : Entails.eval a c35 := h 34 (by decide)
  have h26 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1057 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1057 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c983, some c1052, some c387, some c1056, some c1, some c1053, some c308, some c1042, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1057 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1057 : lratChecker f1057 p1057 = .success := by decide +kernel
theorem unsat1057 : Unsatisfiable (PosFin 57) f1057 := by
  apply lratCheckerSound f1057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1057
  · intro a ha; simp [p1057] at ha; subst a; trivial
  · exact checked1057
theorem derived1057 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1057 := by
  apply localUnsat_implies_entails f1057 [c983, c1052, c387, c1056, c1, c1053, c308, c1042] c1057 unsat1057 (by rfl) a
  have h0 : Entails.eval a c983 := derived983 a h
  have h1 : Entails.eval a c1052 := derived1052 a h
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c1056 := derived1056 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c1053 := derived1053 a h
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c1042 := derived1042 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1058 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1058 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c199, some c159, some c786, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1058 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1058 : lratChecker f1058 p1058 = .success := by decide +kernel
theorem unsat1058 : Unsatisfiable (PosFin 57) f1058 := by
  apply lratCheckerSound f1058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1058
  · intro a ha; simp [p1058] at ha; subst a; trivial
  · exact checked1058
theorem derived1058 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1058 := by
  apply localUnsat_implies_entails f1058 [c1057, c199, c159, c786] c1058 unsat1058 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c786 := derived786 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1059 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1059 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c786, some c327, some c321, some c918, some c64, some c123, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1059 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1059 : lratChecker f1059 p1059 = .success := by decide +kernel
theorem unsat1059 : Unsatisfiable (PosFin 57) f1059 := by
  apply lratCheckerSound f1059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1059
  · intro a ha; simp [p1059] at ha; subst a; trivial
  · exact checked1059
theorem derived1059 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1059 := by
  apply localUnsat_implies_entails f1059 [c1, c786, c327, c321, c918, c64, c123] c1059 unsat1059 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c918 := derived918 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1060 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1060 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c91, some c918, some c376, some c123, some c380, some c112, some c95, some c389, some c109, some c369, some c122, some c382, some c116, some c42, some c254, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1060 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1060 : lratChecker f1060 p1060 = .success := by decide +kernel
theorem unsat1060 : Unsatisfiable (PosFin 57) f1060 := by
  apply lratCheckerSound f1060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1060
  · intro a ha; simp [p1060] at ha; subst a; trivial
  · exact checked1060
theorem derived1060 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1060 := by
  apply localUnsat_implies_entails f1060 [c1057, c91, c918, c376, c123, c380, c112, c95, c389, c109, c369, c122, c382, c116, c42, c254] c1060 unsat1060 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c918 := derived918 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c382 := h 381 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1061 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨45, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1061 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c253, some c392, some c41, some c112, some c123, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1061 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1061 : lratChecker f1061 p1061 = .success := by decide +kernel
theorem unsat1061 : Unsatisfiable (PosFin 57) f1061 := by
  apply lratCheckerSound f1061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1061
  · intro a ha; simp [p1061] at ha; subst a; trivial
  · exact checked1061
theorem derived1061 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1061 := by
  apply localUnsat_implies_entails f1061 [c1060, c253, c392, c41, c112, c123] c1061 unsat1061 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c392 := h 391 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1062 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1062 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c91, some c1, some c8, some c148, some c1058, some c208, some c683, some c195, some c18, some c1061, some c37, some c380, some c291, some c376, some c770, some c392, some c138, some c112, some c41, some c123, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1062 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1062 : lratChecker f1062 p1062 = .success := by decide +kernel
theorem unsat1062 : Unsatisfiable (PosFin 57) f1062 := by
  apply lratCheckerSound f1062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1062
  · intro a ha; simp [p1062] at ha; subst a; trivial
  · exact checked1062
theorem derived1062 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1062 := by
  apply localUnsat_implies_entails f1062 [c1057, c91, c1, c8, c148, c1058, c208, c683, c195, c18, c1061, c37, c380, c291, c376, c770, c392, c138, c112, c41, c123] c1062 unsat1062 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c683 := derived683 a h
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c1061 := derived1061 a h
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c770 := derived770 a h
  have h16 : Entails.eval a c392 := h 391 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c41 := h 40 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1063 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨16, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1063 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c47, some c291, some c136, some c35, some c227, some c140, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1063 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1063 : lratChecker f1063 p1063 = .success := by decide +kernel
theorem unsat1063 : Unsatisfiable (PosFin 57) f1063 := by
  apply lratCheckerSound f1063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1063
  · intro a ha; simp [p1063] at ha; subst a; trivial
  · exact checked1063
theorem derived1063 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1063 := by
  apply localUnsat_implies_entails f1063 [c37, c47, c291, c136, c35, c227, c140] c1063 unsat1063 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c227 := h 226 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1064 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1064 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c78, some c162, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1064 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1064 : lratChecker f1064 p1064 = .success := by decide +kernel
theorem unsat1064 : Unsatisfiable (PosFin 57) f1064 := by
  apply lratCheckerSound f1064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1064
  · intro a ha; simp [p1064] at ha; subst a; trivial
  · exact checked1064
theorem derived1064 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1064 := by
  apply localUnsat_implies_entails f1064 [c342, c78, c162] c1064 unsat1064 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1065 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1065 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c786, some c91, some c1062, some c188, some c1, some c123, some c19, some c112, some c392, some c372, some c183, some c1064, some c145, some c213, some c1063, some c253, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1065 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1065 : lratChecker f1065 p1065 = .success := by decide +kernel
theorem unsat1065 : Unsatisfiable (PosFin 57) f1065 := by
  apply lratCheckerSound f1065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1065
  · intro a ha; simp [p1065] at ha; subst a; trivial
  · exact checked1065
theorem derived1065 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1065 := by
  apply localUnsat_implies_entails f1065 [c1057, c786, c91, c1062, c188, c1, c123, c19, c112, c392, c372, c183, c1064, c145, c213, c1063, c253] c1065 unsat1065 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c1062 := derived1062 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c1064 := derived1064 a h
  have h13 : Entails.eval a c145 := h 144 (by decide)
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c1063 := derived1063 a h
  have h16 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1066 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1066 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c33, some c253, some c138, some c37, some c35, some c291, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1066 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1066 : lratChecker f1066 p1066 = .success := by decide +kernel
theorem unsat1066 : Unsatisfiable (PosFin 57) f1066 := by
  apply lratCheckerSound f1066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1066
  · intro a ha; simp [p1066] at ha; subst a; trivial
  · exact checked1066
theorem derived1066 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1066 := by
  apply localUnsat_implies_entails f1066 [c5, c33, c253, c138, c37, c35, c291] c1066 unsat1066 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1067 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨15, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1067 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c18, some c183, some c94, some c39, some c291, some c135, some c35, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1067 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1067 : lratChecker f1067 p1067 = .success := by decide +kernel
theorem unsat1067 : Unsatisfiable (PosFin 57) f1067 := by
  apply lratCheckerSound f1067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1067
  · intro a ha; simp [p1067] at ha; subst a; trivial
  · exact checked1067
theorem derived1067 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1067 := by
  apply localUnsat_implies_entails f1067 [c1, c18, c183, c94, c39, c291, c135, c35] c1067 unsat1067 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c183 := h 182 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1068 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1068 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c1067, some c1, some c786, some c1065, some c1066, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1068 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1068 : lratChecker f1068 p1068 = .success := by decide +kernel
theorem unsat1068 : Unsatisfiable (PosFin 57) f1068 := by
  apply lratCheckerSound f1068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1068
  · intro a ha; simp [p1068] at ha; subst a; trivial
  · exact checked1068
theorem derived1068 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1068 := by
  apply localUnsat_implies_entails f1068 [c91, c1067, c1, c786, c1065, c1066] c1068 unsat1068 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c1067 := derived1067 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c786 := derived786 a h
  have h4 : Entails.eval a c1065 := derived1065 a h
  have h5 : Entails.eval a c1066 := derived1066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1069 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1069 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c91, some c1062, some c188, some c92, some c1067, some c1068, some c918, some c376, some c123, some c683, some c385, some c19, some c112, some c372, some c389, some c109, some c192, some c122, some c205, some c116, some c6, some c306, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1069 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1069 : lratChecker f1069 p1069 = .success := by decide +kernel
theorem unsat1069 : Unsatisfiable (PosFin 57) f1069 := by
  apply lratCheckerSound f1069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1069
  · intro a ha; simp [p1069] at ha; subst a; trivial
  · exact checked1069
theorem derived1069 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1069 := by
  apply localUnsat_implies_entails f1069 [c1057, c1, c91, c1062, c188, c92, c1067, c1068, c918, c376, c123, c683, c385, c19, c112, c372, c389, c109, c192, c122, c205, c116, c6, c306] c1069 unsat1069 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c1062 := derived1062 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c1067 := derived1067 a h
  have h7 : Entails.eval a c1068 := derived1068 a h
  have h8 : Entails.eval a c918 := derived918 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c683 := derived683 a h
  have h12 : Entails.eval a c385 := h 384 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c372 := h 371 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  have h18 : Entails.eval a c192 := h 191 (by decide)
  have h19 : Entails.eval a c122 := h 121 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  have h22 : Entails.eval a c6 := h 5 (by decide)
  have h23 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1070 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1070 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c19, some c184, some c95, some c40, some c289, some c136, some c33, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1070 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1070 : lratChecker f1070 p1070 = .success := by decide +kernel
theorem unsat1070 : Unsatisfiable (PosFin 57) f1070 := by
  apply lratCheckerSound f1070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1070
  · intro a ha; simp [p1070] at ha; subst a; trivial
  · exact checked1070
theorem derived1070 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1070 := by
  apply localUnsat_implies_entails f1070 [c1, c19, c184, c95, c40, c289, c136, c33] c1070 unsat1070 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1071 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨14, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1071 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c390, some c194, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1071 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1071 : lratChecker f1071 p1071 = .success := by decide +kernel
theorem unsat1071 : Unsatisfiable (PosFin 57) f1071 := by
  apply lratCheckerSound f1071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1071
  · intro a ha; simp [p1071] at ha; subst a; trivial
  · exact checked1071
theorem derived1071 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1071 := by
  apply localUnsat_implies_entails f1071 [c389, c390, c194] c1071 unsat1071 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1072 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨16, by decide⟩, false), (⟨43, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1072 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c206, some c372, some c194, some c180, some c306, some c38, some c821, some c6, some c132, some c83, some c216, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1072 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1072 : lratChecker f1072 p1072 = .success := by decide +kernel
theorem unsat1072 : Unsatisfiable (PosFin 57) f1072 := by
  apply lratCheckerSound f1072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1072
  · intro a ha; simp [p1072] at ha; subst a; trivial
  · exact checked1072
theorem derived1072 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1072 := by
  apply localUnsat_implies_entails f1072 [c1057, c206, c372, c194, c180, c306, c38, c821, c6, c132, c83, c216] c1072 unsat1072 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c821 := derived821 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1073 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨4, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1073 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c306, some c6, some c146, some c81, some c343, some c163, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1073 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1073 : lratChecker f1073 p1073 = .success := by decide +kernel
theorem unsat1073 : Unsatisfiable (PosFin 57) f1073 := by
  apply lratCheckerSound f1073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1073
  · intro a ha; simp [p1073] at ha; subst a; trivial
  · exact checked1073
theorem derived1073 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1073 := by
  apply localUnsat_implies_entails f1073 [c306, c6, c146, c81, c343, c163] c1073 unsat1073 (by rfl) a
  have h0 : Entails.eval a c306 := h 305 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1074 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨47, by decide⟩, true), (⟨11, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨55, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1074 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c1, some c206, some c1071, some c373, some c184, some c1072, some c1073, some c377, some c382, some c38, some c93, some c257, some c132, some c379, some c247, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1074 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1074 : lratChecker f1074 p1074 = .success := by decide +kernel
theorem unsat1074 : Unsatisfiable (PosFin 57) f1074 := by
  apply lratCheckerSound f1074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1074
  · intro a ha; simp [p1074] at ha; subst a; trivial
  · exact checked1074
theorem derived1074 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1074 := by
  apply localUnsat_implies_entails f1074 [c17, c1, c206, c1071, c373, c184, c1072, c1073, c377, c382, c38, c93, c257, c132, c379, c247] c1074 unsat1074 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c1071 := derived1071 a h
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c1072 := derived1072 a h
  have h7 : Entails.eval a c1073 := derived1073 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c379 := h 378 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1075 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨50, by decide⟩, false), (⟨47, by decide⟩, true), (⟨11, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1075 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c195, some c389, some c197, some c373, some c184, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1075 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1075 : lratChecker f1075 p1075 = .success := by decide +kernel
theorem unsat1075 : Unsatisfiable (PosFin 57) f1075 := by
  apply lratCheckerSound f1075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1075
  · intro a ha; simp [p1075] at ha; subst a; trivial
  · exact checked1075
theorem derived1075 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1075 := by
  apply localUnsat_implies_entails f1075 [c1057, c195, c389, c197, c373, c184] c1075 unsat1075 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c389 := h 388 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1076 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1076 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1069, some c124, some c115, some c13, some c89, some c208, some c186, some c1070, some c120, some c492, some c17, some c1075, some c206, some c1074, some c1071, some c384, some c373, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1076 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1076 : lratChecker f1076 p1076 = .success := by decide +kernel
theorem unsat1076 : Unsatisfiable (PosFin 57) f1076 := by
  apply lratCheckerSound f1076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1076
  · intro a ha; simp [p1076] at ha; subst a; trivial
  · exact checked1076
theorem derived1076 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1076 := by
  apply localUnsat_implies_entails f1076 [c1057, c1069, c124, c115, c13, c89, c208, c186, c1070, c120, c492, c17, c1075, c206, c1074, c1071, c384, c373] c1076 unsat1076 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1069 := derived1069 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c1070 := derived1070 a h
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c492 := derived492 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c1075 := derived1075 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c1074 := derived1074 a h
  have h15 : Entails.eval a c1071 := derived1071 a h
  have h16 : Entails.eval a c384 := h 383 (by decide)
  have h17 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1077 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1077 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c199, some c206, some c204, some c198, some c1073, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1077 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1077 : lratChecker f1077 p1077 = .success := by decide +kernel
theorem unsat1077 : Unsatisfiable (PosFin 57) f1077 := by
  apply lratCheckerSound f1077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1077
  · intro a ha; simp [p1077] at ha; subst a; trivial
  · exact checked1077
theorem derived1077 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1077 := by
  apply localUnsat_implies_entails f1077 [c1057, c199, c206, c204, c198, c1073] c1077 unsat1077 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c1073 := derived1073 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1078 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1078 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c6, some c306, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1078 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1078 : lratChecker f1078 p1078 = .success := by decide +kernel
theorem unsat1078 : Unsatisfiable (PosFin 57) f1078 := by
  apply lratCheckerSound f1078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1078
  · intro a ha; simp [p1078] at ha; subst a; trivial
  · exact checked1078
theorem derived1078 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1078 := by
  apply localUnsat_implies_entails f1078 [c198, c6, c306] c1078 unsat1078 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1079 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨16, by decide⟩, false), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1079 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c373, some c374, some c188, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1079 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1079 : lratChecker f1079 p1079 = .success := by decide +kernel
theorem unsat1079 : Unsatisfiable (PosFin 57) f1079 := by
  apply lratCheckerSound f1079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1079
  · intro a ha; simp [p1079] at ha; subst a; trivial
  · exact checked1079
theorem derived1079 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1079 := by
  apply localUnsat_implies_entails f1079 [c1057, c373, c374, c188] c1079 unsat1079 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1080 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1080 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c390, some c110, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1080 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1080 : lratChecker f1080 p1080 = .success := by decide +kernel
theorem unsat1080 : Unsatisfiable (PosFin 57) f1080 := by
  apply lratCheckerSound f1080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1080
  · intro a ha; simp [p1080] at ha; subst a; trivial
  · exact checked1080
theorem derived1080 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1080 := by
  apply localUnsat_implies_entails f1080 [c389, c390, c110] c1080 unsat1080 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1081 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1081 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c208, some c199, some c1080, some c1079, some c13, some c90, some c110, some c382, some c187, some c376, some c384, some c677, some c39, some c378, some c135, some c257, some c245, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1081 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1081 : lratChecker f1081 p1081 = .success := by decide +kernel
theorem unsat1081 : Unsatisfiable (PosFin 57) f1081 := by
  apply lratCheckerSound f1081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1081
  · intro a ha; simp [p1081] at ha; subst a; trivial
  · exact checked1081
theorem derived1081 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1081 := by
  apply localUnsat_implies_entails f1081 [c1057, c208, c199, c1080, c1079, c13, c90, c110, c382, c187, c376, c384, c677, c39, c378, c135, c257, c245] c1081 unsat1081 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c1080 := derived1080 a h
  have h4 : Entails.eval a c1079 := derived1079 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c677 := derived677 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c378 := h 377 (by decide)
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1082 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1082 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1076, some c18, some c208, some c199, some c1069, some c1, some c1077, some c17, some c192, some c121, some c1078, some c1081, some c306, some c34, some c259, some c139, some c254, some c36, some c216, some c46, some c84, some c76, some c135, some c233, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1082 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1082 : lratChecker f1082 p1082 = .success := by decide +kernel
theorem unsat1082 : Unsatisfiable (PosFin 57) f1082 := by
  apply lratCheckerSound f1082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1082
  · intro a ha; simp [p1082] at ha; subst a; trivial
  · exact checked1082
theorem derived1082 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1082 := by
  apply localUnsat_implies_entails f1082 [c1057, c1076, c18, c208, c199, c1069, c1, c1077, c17, c192, c121, c1078, c1081, c306, c34, c259, c139, c254, c36, c216, c46, c84, c76, c135, c233] c1082 unsat1082 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1076 := derived1076 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c1069 := derived1069 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c1077 := derived1077 a h
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c1078 := derived1078 a h
  have h12 : Entails.eval a c1081 := derived1081 a h
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c34 := h 33 (by decide)
  have h15 : Entails.eval a c259 := h 258 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c216 := h 215 (by decide)
  have h20 : Entails.eval a c46 := h 45 (by decide)
  have h21 : Entails.eval a c84 := h 83 (by decide)
  have h22 : Entails.eval a c76 := h 75 (by decide)
  have h23 : Entails.eval a c135 := h 134 (by decide)
  have h24 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1083 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1083 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c88, some c113, some c181, some c122, some c98, some c1078, some c830, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1083 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1083 : lratChecker f1083 p1083 = .success := by decide +kernel
theorem unsat1083 : Unsatisfiable (PosFin 57) f1083 := by
  apply lratCheckerSound f1083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1083
  · intro a ha; simp [p1083] at ha; subst a; trivial
  · exact checked1083
theorem derived1083 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1083 := by
  apply localUnsat_implies_entails f1083 [c1057, c88, c113, c181, c122, c98, c1078, c830] c1083 unsat1083 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c1078 := derived1078 a h
  have h7 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1084 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c1076, some c18, some c208, some c1082, some c19, some c204, some c17, some c192, some c1083, some c389, some c1080, some c111, some c122, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 57) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c1057, c1, c1076, c18, c208, c1082, c19, c204, c17, c192, c1083, c389, c1080, c111, c122] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1076 := derived1076 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c1082 := derived1082 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c1083 := derived1083 a h
  have h11 : Entails.eval a c389 := h 388 (by decide)
  have h12 : Entails.eval a c1080 := derived1080 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c113, some c111, some c392, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c1057, c113, c111, c392] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c158, some c62, some c34, some c324, some c139, some c137, some c225, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c159, c158, c62, c34, c324, c139, c137, c225] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1069, some c1084, some c786, some c5, some c124, some c18, some c145, some c342, some c159, some c1, some c80, some c163, some c204, some c17, some c152, some c121, some c1086, some c306, some c14, some c90, some c110, some c185, some c392, some c1079, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1069, c1084, c786, c5, c124, c18, c145, c342, c159, c1, c80, c163, c204, c17, c152, c121, c1086, c306, c14, c90, c110, c185, c392, c1079] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1069 := derived1069 a h
  have h1 : Entails.eval a c1084 := derived1084 a h
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c159 := h 158 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c1086 := derived1086 a h
  have h17 : Entails.eval a c306 := h 305 (by decide)
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c392 := h 391 (by decide)
  have h23 : Entails.eval a c1079 := derived1079 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1084, some c786, some c1069, some c1, some c145, some c5, some c342, some c124, some c18, some c1087, some c19, some c1085, some c204, some c17, some c152, some c161, some c122, some c76, some c1086, some c306, some c325, some c14, some c90, some c428, some c830, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c1084, c786, c1069, c1, c145, c5, c342, c124, c18, c1087, c19, c1085, c204, c17, c152, c161, c122, c76, c1086, c306, c325, c14, c90, c428, c830] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c1084 := derived1084 a h
  have h1 : Entails.eval a c786 := derived786 a h
  have h2 : Entails.eval a c1069 := derived1069 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c1087 := derived1087 a h
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c1085 := derived1085 a h
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c161 := h 160 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c76 := h 75 (by decide)
  have h18 : Entails.eval a c1086 := derived1086 a h
  have h19 : Entails.eval a c306 := h 305 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  have h21 : Entails.eval a c14 := h 13 (by decide)
  have h22 : Entails.eval a c90 := h 89 (by decide)
  have h23 : Entails.eval a c428 := derived428 a h
  have h24 : Entails.eval a c830 := derived830 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c47, some c136, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 57) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c19, c47, c136] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c205, some c514, some c212, some c225, some c77, some c132, some c167, some c162, some c166, some c359, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 57) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c136, c205, c514, c212, c225, c77, c132, c167, c162, c166, c359] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c514 := derived514 a h
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c225 := h 224 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c120, some c60, some c67, some c342, some c287, some c84, some c359, some c236, some c789, some c77, some c166, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 57) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c124, c120, c60, c67, c342, c287, c84, c359, c236, c789, c77, c166] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c789 := derived789 a h
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c33, some c253, some c1091, some c162, some c231, some c77, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 57) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c124, c33, c253, c1091, c162, c231, c77] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c1091 := derived1091 a h
  have h4 : Entails.eval a c162 := h 161 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1057, some c1, some c1069, some c1084, some c786, some c1088, some c208, some c18, some c124, some c33, some c253, some c138, some c1089, some c120, some c17, some c60, some c45, some c1090, some c1092, some c264, some c273, some c197, some c206, some c1073, some c903, some c14, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p1093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 57) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c1057, c1, c1069, c1084, c786, c1088, c208, c18, c124, c33, c253, c138, c1089, c120, c17, c60, c45, c1090, c1092, c264, c273, c197, c206, c1073, c903, c14] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c1057 := derived1057 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c1069 := derived1069 a h
  have h3 : Entails.eval a c1084 := derived1084 a h
  have h4 : Entails.eval a c786 := derived786 a h
  have h5 : Entails.eval a c1088 := derived1088 a h
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c253 := h 252 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c1089 := derived1089 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c1090 := derived1090 a h
  have h18 : Entails.eval a c1092 := derived1092 a h
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c273 := h 272 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c206 := h 205 (by decide)
  have h23 : Entails.eval a c1073 := derived1073 a h
  have h24 : Entails.eval a c903 := derived903 a h
  have h25 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1093

end CochromaticTwenty.Certificates.B16_1_2
